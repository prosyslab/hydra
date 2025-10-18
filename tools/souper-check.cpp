// Copyright 2014 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/KnownBits.h"

#include "souper/Infer/ConstantSynthesis.h"
#include "souper/Infer/Pruning.h"
#include "souper/Infer/SynthUtils.h"
#include "souper/Infer/Invariants.h"
#include "souper/Inst/InstGraph.h"
#include "souper/Parser/Parser.h"
#include "souper/Tool/GetSolver.h"
#include "souper/Util/DfaUtils.h"

using namespace llvm;

namespace souper {
  Solver *S;
}

using namespace souper;

unsigned DebugLevel = 2;

// static cl::opt<unsigned, /*ExternalStorage=*/true>
// DebugFlagParser("souper-debug-level",
//      cl::desc("Control the verbose level of debug output (default=1). "
//      "The larger the number is, the more fine-grained debug "
//      "information will be printed."),
//      cl::location(DebugLevel), cl::init(1));

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input souper optimization>"),
              cl::init("-"));

static cl::opt<bool> PrintCounterExample("print-counterexample",
    cl::desc("Print counterexample (default=true)"),
    cl::init(true));

static cl::opt<bool> PrintRepl("print-replacement",
    cl::desc("Print the replacement, if valid (default=false)"),
    cl::init(false));

static cl::opt<bool> PrintReplSplit("print-replacement-split", cl::Hidden,
    cl::desc("Print the replacement as an infer/result pair (default=false)"),
    cl::init(false));

static cl::opt<bool> InferRHS("infer-rhs",
    cl::desc("Try to infer a RHS for a Souper LHS (default=false)"),
    cl::init(false));

static cl::opt<bool> SymInferRHS("sym-infer-rhs",
    cl::desc("Try to infer RHS for a Souper Symbolic LHS (default=false)"),
    cl::init(false));

static cl::opt<bool> InferConst("infer-const",
    cl::desc("Try to infer constants for a Souper replacement (default=false)"),
    cl::init(false));

static cl::opt<bool> InferConstOnlyPrintConsts("infer-const-only-print-consts",
    cl::desc("Only print synthesized constants (default=false)"),
    cl::init(false));

static cl::list<std::string> InferConstBlockList("infer-const-blocklist",
    cl::desc("Constant synthesis blocklist"), cl::CommaSeparated);

static cl::opt<bool> ReInferRHS("reinfer-rhs",
    cl::desc("Try to infer a new RHS and compare its cost with the existing RHS (default=false)"),
    cl::init(false));

static cl::opt<bool> ParseOnly("parse-only",
    cl::desc("Only parse the replacement, don't call isValid() (default=false)"),
    cl::init(false));

static cl::opt<bool> ParseLHSOnly("parse-lhs-only",
    cl::desc("Only parse the LHS, don't call infer() (default=false)"),
    cl::init(false));

static cl::opt<bool> EmitLHSDot("emit-lhs-dot",
    cl::desc("Emit DOT format DAG for LHS of given souper IR (default=false)"),
    cl::init(false));

static cl::opt<bool> TryDataflowPruning("try-dataflow-pruning",
    cl::desc("Attempt to prove inequivalence using dataflow analysis (default=false)"),
    cl::init(false));

static cl::opt<bool> CheckAllGuesses("souper-check-all-guesses",
    cl::desc("Continue even after a valid RHS is found. (default=false)"),
    cl::init(false));

static cl::opt<bool> Hash("hash",
    cl::desc("Hash a trasnformation. (default=false)"),
    cl::init(false));

static cl::opt<bool> FixIt("fixit",
    cl::desc("Replace constants with ones that work. (default=false)"),
    cl::init(false));

// static cl::opt<bool> InferInv("infer-invariants",
//     cl::desc("Infer invariants. (default=false)"),
//     cl::init(false));

static cl::opt<bool> VerifyInv("verify-invariants",
    cl::desc("Verify invariants. (default=false)"),
    cl::init(false));

static cl::opt<bool> FilterRedundant("filter-redundant",
    cl::desc("Filter redundant transformations based on static hashing (default=false)"),
    cl::init(false));

static cl::opt<std::string> PrettyPrint("pretty-print",
    cl::desc("Pretty print (default=null)"),
    cl::init(""));

static cl::opt<bool> PrintProfit("print-profit",
    cl::desc("Print profit (default=false)"),
    cl::init(false));


size_t HashInt(size_t x) {
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  x = x ^ (x >> 31);
  return x;
}

size_t HashInst(Inst *I, std::map<Inst *, size_t> &M, std::set<Inst *> &SeenVars) {
  if (M.find(I) != M.end()) {
    return M[I];
  }

  size_t Result = 0;

//  if (I->Name != "") {
//    Result ^= std::hash<std::string>()(I->Name);
//  }

  Result ^= HashInt(I->K);

  if (I->K == Inst::Var) {
    SeenVars.insert(I);
    Result ^= HashInt(SeenVars.size());
    // TODO: DF attributes
    M[I] = Result;
  }

  if (I->K == Inst::Const) {
    Result ^= HashInt(I->Val.getLimitedValue());
  }

  for (size_t i = 0; i < I->Ops.size(); ++i) {
    size_t Weight = Inst::isCommutative(I->K) ? 0 : HashInt(i);

    Result ^= (Weight + HashInst(I->Ops[i], M, SeenVars));
  }

  M[I] = Result;
  return Result;
}

size_t HashRep(ParsedReplacement Rep) {
  std::map<Inst *, size_t> M;
  std::set<Inst *> SeenVars;
  auto Result = HashInst(Rep.Mapping.LHS, M, SeenVars);
  Result ^= 7* HashInst(Rep.Mapping.RHS, M, SeenVars);
  // Just ^ produces weird conflicts for very different trees

  // Is this needed?
  Result ^= HashInt(Rep.Mapping.LHS->Width);

  for (auto PC : Rep.PCs)  {
    Result ^= HashInst(PC.LHS, M, SeenVars);
    Result ^= HashInst(PC.RHS, M, SeenVars);
  }

  return Result;
}

int SolveInst(const MemoryBufferRef &MB, Solver *S) {
  InstContext IC;
  std::string ErrStr;

  std::vector<ParsedReplacement> Reps;
  std::vector<ReplacementContext> Contexts;
  if (SymInferRHS || InferRHS || ParseLHSOnly || isInferDFA()) {
    Reps = ParseReplacementLHSs(IC, MB.getBufferIdentifier(), MB.getBuffer(),
                                Contexts, ErrStr);
  } else {
    Reps = ParseReplacements(IC, MB.getBufferIdentifier(), MB.getBuffer(), ErrStr);
  }
  if (!ErrStr.empty()) {
    llvm::errs() << ErrStr << '\n';
    return 1;
  }

  if (EmitLHSDot) {
    llvm::outs() << "; emitting DOT for parsed LHS souper IR ...\n";
    for (auto &Rep : Reps) {
      llvm::WriteGraph(llvm::outs(), Rep.Mapping.LHS);
    }
  }

  if (ParseOnly || ParseLHSOnly) {
    llvm::outs() << "; parsing successful\n";
    return 0;
  }

  unsigned Index = 0;
  int Ret = 0;
  int Success = 0, Fail = 0, Error = 0;

  std::unordered_set<size_t> Hashes;

  for (auto Rep : Reps) {
    if (Hash) {
      llvm::outs() << HashRep(Rep) << '\n';
      continue;
    }

    if (FilterRedundant) {
      auto Hash = HashRep(Rep);
      if (Hashes.find(Hash) == Hashes.end()) {
        Hashes.insert(Hash);

        bool Valid;
        std::vector<std::pair<Inst *, APInt>> Models;
        if (std::error_code EC = S->isValid(IC, Rep.BPCs, Rep.PCs,
                                            Rep.Mapping, Valid, &Models)) {
          llvm::errs() << EC.message() << '\n';
          Ret = 1;
          ++Error;
        }

        if (Valid) {
          ReplacementContext RC;
          Rep.printLHS(llvm::outs(), RC, true);
          Rep.printRHS(llvm::outs(), RC, true);
        } else {
          // TODO: Warn about invalid transformation.
        }
      } else {
        llvm::outs() << "; Skipping redundant transformation.\n";
        std::string S;
        llvm::raw_string_ostream Str(S);
        ReplacementContext RC;
        Rep.printLHS(Str, RC, true);
        Rep.printRHS(Str, RC, true);
        Str.flush();
        llvm::outs() << ';';
        for (size_t i = 0; i < S.length(); ++i) {
          auto c = S[i];
          if ((c == '\n' || c == '\r') && i != S.length() - 1) {
            llvm::outs() << c << ';';
          } else {
            llvm::outs() << c;
          }
        }
      }
      continue;
    }

    if (isInferDFA()) {
      if (InferNeg) {
        bool Negative;
        if (std::error_code EC = S->negative(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                             Negative, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "negative from souper: "
                       << convertToStr(Negative) << "\n";
          ++Success;
        }
      }
      if (InferNonNeg) {
        bool NonNegative;
        if (std::error_code EC = S->nonNegative(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                                NonNegative, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "nonNegative from souper: "
                       << convertToStr(NonNegative) << "\n";
          ++Success;
        }
      }
      if (InferKnownBits) {
        unsigned W = Rep.Mapping.LHS->Width;
        KnownBits Known(W);
        if (std::error_code EC = S->knownBits(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                              Known, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "knownBits from souper: "
                       << Inst::getKnownBitsString(Known.Zero, Known.One) << "\n";
          ++Success;
        }
      }
      if (InferPowerTwo) {
        bool PowTwo;
        if (std::error_code EC = S->powerTwo(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                             PowTwo, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "powerOfTwo from souper: "
                       << convertToStr(PowTwo) << "\n";
          ++Success;
        }
      }
      if (InferNonZero) {
        bool NonZero;
        if (std::error_code EC = S->nonZero(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                            NonZero, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "nonZero from souper: "
                       << convertToStr(NonZero) << "\n";
          ++Success;
        }
      }
      if (InferSignBits) {
        unsigned SignBits;
        if (std::error_code EC = S->signBits(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                             SignBits, IC)) {
          llvm::errs() << "Error: " << EC.message() << '\n';
          Ret = 1;
          ++Error;
        } else {
          llvm::outs() << "signBits from souper: "
                       << std::to_string(SignBits) << "\n";
          ++Success;
        }
      }
      if (InferRange) {
        unsigned W = Rep.Mapping.LHS->Width;
        llvm::ConstantRange Range = S->constantRange(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS, IC);

        llvm::outs() << "range from souper: " << "[" << Range.getLower()
                     << "," << Range.getUpper() << ")" << "\n";
        ++Success;
      }
      if (InferDemandedBits) {
        std::map<std::string, APInt> DBitsVect;
        if (std::error_code EC = S->testDemandedBits(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                                     DBitsVect, IC)) {
          llvm::errs() << EC.message() << '\n';
        }
        for (std::map<std::string,APInt>::iterator I = DBitsVect.begin();
             I != DBitsVect.end(); ++I) {
          std::string VarName = I->first;
          llvm::APInt DBitsVar = DBitsVect[VarName];
          std::string s = Inst::getDemandedBitsString(DBitsVar);
          llvm::outs() << "demanded-bits from souper for %" << VarName << " : "<< s << "\n";
        }
        return 0;
      }
    } else if (InferRHS || ReInferRHS || SymInferRHS) {
      int OldCost;
      std::vector<Inst *> RHSs;
      if (ReInferRHS) {
        OldCost = cost(Rep.Mapping.RHS);
        Rep.Mapping.RHS = 0;
      }
      if (std::error_code EC = S->infer(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                        RHSs, CheckAllGuesses, IC)) {
        llvm::errs() << EC.message() << '\n';
        Ret = 1;
        ++Error;
      }
      if (!RHSs.empty()) {
        Rep.Mapping.RHS = RHSs.front();
        ++Success;
        if (ReInferRHS) {
          int NewCost = cost(Rep.Mapping.RHS);
          int LHSCost = cost(Rep.Mapping.LHS);
          if (NewCost <= OldCost)
            llvm::outs() << "; RHS inferred successfully, no cost regression";
          else
            llvm::outs() << "; RHS inferred successfully, but cost regressed";
          llvm::outs() << " (Old= " << OldCost << ", New= " << NewCost <<
            ", LHS= " << LHSCost << ")\n";
        } else {
          llvm::outs() << "; RHS inferred successfully\n";
        }

        if (CheckAllGuesses) {
          for (unsigned RI = 0 ; RI < RHSs.size(); RI++) {
            llvm::outs() << "; result " << (RI + 1) << ":\n";
            if (PrintRepl || PrintReplSplit) {
              ReplacementContext RC;
              PrintReplacementLHS(llvm::outs(), Rep.BPCs, Rep.PCs,
                Rep.Mapping.LHS, RC, true);
              PrintReplacementRHS(llvm::outs(), RHSs[RI], RC, true);
              llvm::outs() << "\n";
            } else {
              ReplacementContext RC;
              PrintReplacementRHS(llvm::outs(), RHSs[RI], RC);
              llvm::outs() << "\n";
            }
          }
        } else {
          if (PrintRepl) {
            PrintReplacement(llvm::outs(), Rep.BPCs, Rep.PCs, Rep.Mapping);
          } else if (PrintReplSplit) {
            ReplacementContext Context;
            PrintReplacementLHS(llvm::outs(), Rep.BPCs, Rep.PCs,
                                Rep.Mapping.LHS, Context);
            PrintReplacementRHS(llvm::outs(), Rep.Mapping.RHS, Context);
          } else if (SymInferRHS) {
            ReplacementContext Context;
            PrintReplacementLHS(llvm::outs(), Rep.BPCs, Rep.PCs,
                                Rep.Mapping.RHS->Aux, Context);
            PrintReplacementRHS(llvm::outs(), Rep.Mapping.RHS, Context);
          } else {
            ReplacementContext Context;
            PrintReplacementRHS(llvm::outs(), Rep.Mapping.RHS,
                                ReInferRHS ? Context : Contexts[Index]);
          }
        }
      } else {
        ++Fail;
        llvm::outs() << "; Failed to infer RHS\n";
        if (PrintRepl || PrintReplSplit) {
          ReplacementContext Context;
          PrintReplacementLHS(llvm::outs(), Rep.BPCs, Rep.PCs,
                              Rep.Mapping.LHS, Context);
        }
      }
    } else if (InferConst) {
      ConstantSynthesis CS;
      std::map <Inst *, llvm::APInt> ResultConstMap;

      std::set<Inst *> ConstSet;
      souper::getConstants(Rep.Mapping.RHS, ConstSet);
      souper::getConstants(Rep.Mapping.LHS, ConstSet);

      if (InferConstBlockList.size() > 1) {
        std::map<std::string, Inst *> Consts;
        for (auto C : ConstSet) {
          Consts[C->Name] = C;
        }

        std::map<std::string, std::vector<int64_t>> BlockList;
        std::string last;
        for (auto S : InferConstBlockList) {
          // if S can not be parsed as a number
          if (S.find_first_not_of("-0123456789") != std::string::npos) {
            last = S;
          } else {
            BlockList[last].push_back(std::stoll(S));
          }
        }

        for (auto S : BlockList) {
          if (DebugLevel > 2) {
            llvm::outs() << "; BlockList: " << S.first << " : ";
          }
          for (auto I : S.second) {
            if (DebugLevel > 2) {
              llvm::outs() << I << " ";
            }
            Rep.PCs.push_back(InstMapping{
              IC.getInst(Inst::Ne, 1,
                          {Consts[S.first],
                            IC.getConst(APInt(Consts[S.first]->Width, I, true))}),
              IC.getConst(APInt(1, 1))
            });
          }
          if (DebugLevel > 2) {
            llvm::outs() << "\n";
          }
        }
      }

      if (ConstSet.empty()) {
        llvm::outs() << "; No reservedconst found in RHS\n";
      } else {
        if (std::error_code EC = S->inferConst(Rep.BPCs, Rep.PCs,
                                               Rep.Mapping.LHS, Rep.Mapping.RHS,
                                               ConstSet, ResultConstMap, IC)) {
          llvm::errs() << EC.message() << '\n';
          Ret = 1;
          ++Error;
        }

        if (!ResultConstMap.empty()) {
          if (InferConstOnlyPrintConsts) {
            for (auto &Const : ResultConstMap) {
              llvm::outs() << Const.first->Name << "  ";
              Const.second.print(llvm::outs(), false);
              llvm::outs() << "\n";
            }
          } else {
            std::map<Inst *, Inst *> InstCache;
            std::map<Block *, Block *> BlockCache;
            Rep.Mapping.LHS =
                getInstCopy(Rep.Mapping.LHS, IC, InstCache, BlockCache, &ResultConstMap, false, false);
            Rep.Mapping.RHS =
                getInstCopy(Rep.Mapping.RHS, IC, InstCache, BlockCache, &ResultConstMap, false, false);
            Rep.print(llvm::outs(), true);
          }
          ++Success;
        } else {
          ++Fail;
          llvm::outs() << "; Failed to synthesize constant(s)\n";
        }
      }
    } else if (TryDataflowPruning) {
      SynthesisContext SC{IC, /*Solver(UNUSED)*/nullptr, Rep.Mapping.LHS,
        /*LHSUB(UNUSED)*/nullptr, Rep.PCs, Rep.BPCs,
        /*CheckAllGuesses(UNUSED)*/true, /*Timeout(UNUSED)*/100};
      std::vector<Inst *> Inputs;
      findVars(SC.LHS, Inputs);
      PruningManager P(SC, Inputs, /*StatsLevel=*/3);
      P.init();
      if (P.isInfeasible(Rep.Mapping.RHS, /*StatsLevel=*/3)) {
        llvm::outs() << "Pruning succeeded.\n";
      } else {
        llvm::outs() << "Pruning failed.\n";
      }
    } else if (FixIt) {
      if (Verify(Rep)) {
        Rep.print(llvm::outs(), true);
      } else {
        // Find RHS-fresh constants
        std::vector<Inst *> LHSConsts, RHSConsts;
        findInsts(Rep.Mapping.LHS, LHSConsts, [](Inst *I) {
          return I->K == Inst::Const;
        });
        findInsts(Rep.Mapping.RHS, RHSConsts, [](Inst *I) {
          return I->K == Inst::Const;
        });
        std::set<Inst *> LHSConstSet(LHSConsts.begin(), LHSConsts.end());
        std::set<Inst *> RHSConstSet(RHSConsts.begin(), RHSConsts.end());
        std::vector<Inst *> FreshConsts;
        for (auto &&C : RHSConstSet) {
          if (LHSConstSet.find(C) == LHSConstSet.end()) {
            FreshConsts.push_back(C);
          }
        }
        std::map<Inst *, Inst *> InstCache;
        std::set<Inst *> ConstSet;
        unsigned ConstID = 1;
        for (auto &&C : FreshConsts) {
          InstCache[C] = IC.createSynthesisConstant(C->Width, ConstID++);
          ConstSet.insert(InstCache[C]);
        }
        auto Clone = Replace(Rep, InstCache);
        if (auto Fixed = Verify(Clone)) {
          ReplacementContext RC;
          Fixed->printLHS(llvm::outs(), RC, true);
          Fixed->printRHS(llvm::outs(), RC, true);
        } else {
          llvm::errs() << "Failed to fix the replacement.\n";
        }
      }
    } else if (PrettyPrint != "") {
      if (PrettyPrint == "infix") {
        InfixPrinter P(Rep);
        P(llvm::outs());
      } else if (PrettyPrint == "latex" || PrettyPrint == "tex") {
        LatexPrinter P(Rep);
        P(llvm::outs());
      } else if (PrettyPrint == "go" || PrettyPrint == "s-expr") {
        GoPrinter P(Rep);
        P(llvm::outs());
      } else if (PrettyPrint == "pdl") {
        static size_t Counter = 0;
        PDLGenerator P(Rep, "opt" + std::to_string(Counter++));
        P(llvm::outs());
      } else {
        llvm_unreachable("unknown pretty-printer");
      }
    } else if (PrintProfit) {
      if (Rep.Mapping.RHS == Rep.Mapping.LHS) {
        llvm::outs() << "-1\n";
        // extra penalty for LHS == RHS
      } else {
        llvm::outs() << souper::profit(Rep) << '\n';
      }
    } else if (VerifyInv) {
      if (VerifyInvariant(Rep)) {
        llvm::outs() << "; LGTM\n";
      } else {
        llvm::outs() << "; Failed to verify invariant\n";
      }
    } else {
      bool Valid;
      std::vector<std::pair<Inst *, APInt>> Models;
      if (std::error_code EC = S->isValid(IC, Rep.BPCs, Rep.PCs,
                                          Rep.Mapping, Valid, &Models)) {
        llvm::errs() << EC.message() << '\n';
        Ret = 1;
        ++Error;
      }

      if (Valid) {
        ++Success;
        llvm::outs() << "; LGTM\n";
        if (PrintRepl)
          PrintReplacement(llvm::outs(), Rep.BPCs, Rep.PCs, Rep.Mapping);
        if (PrintReplSplit) {
          ReplacementContext Context;
          PrintReplacementLHS(llvm::outs(), Rep.BPCs, Rep.PCs,
                              Rep.Mapping.LHS, Context);
          PrintReplacementRHS(llvm::outs(), Rep.Mapping.RHS, Context);
        }
      } else {
        ++Fail;
        llvm::outs() << "Invalid";
        if (PrintCounterExample && !Models.empty()) {
          llvm::outs() << ", e.g.\n\n";
          std::sort(Models.begin(), Models.end(),
                    [](const std::pair<Inst *, APInt> &A,
                       const std::pair<Inst *, APInt> &B) {
                      return A.first->Name < B.first->Name;
                    });
          for (const auto &M : Models) {
            llvm::outs() << '%' << M.first->Name << " = " << M.second << '\n';
          }
        } else {
          llvm::outs() << "\n";
        }
      }
    }
    ++Index;
    if (PrintRepl || PrintReplSplit)
      llvm::outs() << "\n";
  }
  if ((Success + Fail + Error) > 1)
    llvm::outs() << "successes = " << Success << ", failures = " << Fail <<
      ", errors = " << Error << "\n";
  return Ret;
}

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);
  KVStore *KV = 0;

  std::unique_ptr<Solver> S_ = 0;
  if (!ParseOnly && !ParseLHSOnly)
    S_ = GetSolver(KV);

  S = S_.get();

  auto MB = MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (!MB) {
    llvm::errs() << MB.getError().message() << '\n';
    return 1;
  }
  return SolveInst((*MB)->getMemBufferRef(), S);
}
