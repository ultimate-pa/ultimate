//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-12
*/

struct str {
  int a;
  int b;
};

int sum(int count,...) {
   int result = 0;
   
   __builtin_va_list valist;
   __builtin_va_start(valist, count);

   for (int i = 0; i < count; i++) {
      struct str s = __builtin_va_arg(valist, struct str);
      result += s.a - s.b;
   }

   __builtin_va_end(valist);

   return result;
}

int main() {
  struct str s1 = {4, 2};
  struct str s2 = {0, -1};
  int x = sum(2, s1, s2);
  //@ assert x == 3;
}