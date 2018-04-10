// This file is used internally by the build system
// to detect what compiler is being used.
#if defined(__GNUC__) && !defined(__clang__)
  SVCOMP_C_COMPILER_IS_GCC
#elif defined(__GNUC__) && defined(__clang__)
  SVCOMP_C_COMPILER_IS_CLANG
#else
#error Unknown C Compiler
#endif
