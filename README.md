# TL;DR 

```
fish build.fish
fish exp.fish

cd hydra-outputs
rg "Generalized" | wc -l
```


Hydra is based on [Souper](https://github.com/google/souper)

# Requirements

Souper should work on any reasonably modern Linux or OS X machine.

You will need a reasonably modern compiler toolchain. LLVM has instructions
on how to get one for Linux:
http://llvm.org/docs/GettingStarted.html#getting-a-modern-host-c-toolchain

You will also need CMake to build Souper and its dependencies, and the zstd
library from your package manager or from Homebrew.

# Building Souper and Hydra

1. Download and build dependencies:
```
$ ./build_deps.sh $buildtype $extra_cmake_flags
```
   $buildtype is optional; it defaults to Release and may be set to any LLVM
   build type.
   $extra_cmake_flags is optional. It is passed to CMake.

2. Run CMake from a build directory:
```
$ mkdir /path/to/souper-build
$ cd /path/to/souper-build
$ cmake -DCMAKE_BUILD_TYPE=$buildtype /path/to/souper
```
   Again, the build type is optional and defaults to Release. In any case it
   must match the build type used when compiling the dependencies.

3. Run 'make' from the build directory.

4. Optionally run 'make check' to run Souper's test suite. To run the test suite
   under Valgrind, run 'make check LIT_ARGS="-v --vg --vg-leak"' instead. By
   default the solver is also run under Valgrind. This can be disabled by
   by adding --vg-arg=--trace-children-skip=/path/to/solver to LIT_ARGS.

Note that GCC 4.8 and earlier have a bug in handling multiline string
literals. You should build Souper using GCC 4.9+ or Clang.

5. These steps should build hydra automatically. The tool is available in the
   build directory and works on Souper IR.
