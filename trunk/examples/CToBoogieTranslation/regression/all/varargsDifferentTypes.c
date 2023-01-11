//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-05
*/

void check(int count,...) {
   int result = 0;
   
   __builtin_va_list valist;
   __builtin_va_start(valist, count);
   
   char* string = __builtin_va_arg(valist, char*);
   int expected = __builtin_va_arg(valist, int);

   for (int i = 0; i < count; i++) {
      int index = __builtin_va_arg(valist, int);
      char stringAtIndex = string[index];
      //@ assert stringAtIndex == expected;
   }

   __builtin_va_end(valist);
}

int main() {
  check(2, "test",'t',0,3);
  check(0, "abc",'t');
}