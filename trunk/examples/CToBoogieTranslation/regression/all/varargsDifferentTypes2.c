//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-07
*/

void check(int count,...) {
   int result = 0;
   
   __builtin_va_list valist;
   __builtin_va_start(valist, count);
   
   char* string = __builtin_va_arg(valist, char*);
   int actuallyChar = __builtin_va_arg(valist, int);
   long long value = __builtin_va_arg(valist, long long);
   
   //@ assert value == 42;

   __builtin_va_end(valist);
}

int main() {
  check(0, "test",'t',42LL);
}