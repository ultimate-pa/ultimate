//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-05
*/

int sum(int count,...) {
   int result = 0;
   
   __builtin_va_list valist;
   __builtin_va_start(valist, count);

   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(valist, int);
   }

   __builtin_va_end(valist);

   return result;
}

int main() {
  int x = sum(3, 1,2,3);
  //@ assert x == 6;
}