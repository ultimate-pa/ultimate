//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-12
*/

int sum(int count,...) {
   int result = 0;
   
   va_list valist;
   va_start(valist, count);

   for (int i = 0; i < count; i++) {
      result += va_arg(valist, int);
   }

   va_end(valist);

   return result;
}

int main() {
  int x = sum(3, 1,2,3);
  //@ assert x == 6;
}
