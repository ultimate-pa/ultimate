//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-05
*/

void isSorted(int count,...) {
   int result = 0;
   
   __builtin_va_list valist;
   __builtin_va_start(valist, count);
   
   long long lastValue = -1;

   for (int i = 0; i < count; i++) {
      long long value = __builtin_va_arg(valist, long long);
      //@ assert value >= lastValue;
      lastValue = value;
   }

   __builtin_va_end(valist);
}

int main() {
  isSorted(3, 0LL,1LL,3LL);
  isSorted(2, 1LL,2LL);
}