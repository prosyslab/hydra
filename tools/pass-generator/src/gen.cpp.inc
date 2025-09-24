Value *f(llvm::Instruction *I, IRBuilder *B) {
if (I->getOpcode() == Instruction::Add) {
/* Opt : 0
%symconst_1:i8 = var ; symconst_1
%newvar0:i8 = var ; newvar0
%symconst_2:i8 = var ; symconst_2
%3:i8 = add %newvar0, %symconst_2
%4:i8 = add %symconst_1, %3
infer %4
%5:i8 = add %symconst_1, %symconst_2
%6:i8 = add %newvar0, %5
result %6

C1 + (C2 + newvar0)
  =>
newvar0 + (C2 + C1)
*/
{
llvm::Value *x2 = nullptr, *x1 = nullptr, *x0 = nullptr, *x3 = nullptr, *x4 = nullptr;
if (util::filter(F, 0) && match(I, m_c_Add(m_Constant(&x2), &x3 <<= m_c_Add(m_Value(x1), m_Constant(&x0))))) {
if (util::dc(DT, I, x1)) {
  auto ret = B->CreateAdd(x1, B->CreateAdd(x2, x0));
if (util::check_width(ret, I)) {
  St.hit(I, 0, 1);
  St.elims(0, x3, x4);
  return ret;

}
}
}}

}

 return nullptr;
}