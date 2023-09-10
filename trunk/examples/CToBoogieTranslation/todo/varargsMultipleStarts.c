//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-07
*/

int doubleSum(int count,...) {
   int result = 0;
   
   __builtin_va_list v1, v2;
   
   __builtin_va_start(v1, count);
   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(v1, int);
   }
   __builtin_va_end(v1);
   
   __builtin_va_start(v2, count);
   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(v2, int);
   }
   __builtin_va_end(v2);

   return result;
}

int main() {
  int x = doubleSum(3, 1,2,3);
  //@ assert x == 12;
}
