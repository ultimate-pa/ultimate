//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-07
*/

extern int varArgFunction(char const * , ...);

int varArgFunction(char const *format, ...) {
  __builtin_va_list v;
  __builtin_va_start(v, format);
  
  int result = __builtin_va_arg(v, int);
  
  __builtin_va_end(v);
  return result;
}

int main() {
  int x = varArgFunction("%d, %d", 1, 2);
  //@ assert x == 1;
}
