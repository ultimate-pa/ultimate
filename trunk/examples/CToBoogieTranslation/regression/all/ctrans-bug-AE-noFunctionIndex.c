//#Safe
/*
2018-09-13  DD

Example for 
AssertionError: main is not PRDispatcher and getFunctionToIndex is empty, but want to process (*__cil_tmp10) as function pointer
at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler.handleFunctionPointerCall(FunctionHandler.java:398)

*/ 

void foo(int (*myfun)()) {
  int (*bar)();
  bar = (int(*)()) myfun;
  bar();
}


