//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-17-03
*/

int sum(int count,...) {
   int result = 0;
   
   __builtin_va_list* v = malloc(sizeof(__builtin_va_list));
   __builtin_va_start(*v, count);
   
   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(*v, int);
   }

   __builtin_va_end(*v);
	 free(v);

   return result;
}

int main() {
  int x = sum(3, 1,2,3);
  //@ assert x == 6;
}
