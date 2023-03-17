//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-17-03

	Currently va_copy is only handled by overapproximation.
*/

int doubleSum(int count,...) {
   int result = 0;
   
   __builtin_va_list* v = malloc(2 * sizeof(__builtin_va_list));
   __builtin_va_start(v[0], count);
   __builtin_va_copy(v[1], v[0]);
   
   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(v[0], int);
   }
   for (int i = 0; i < count; i++) {
      result += __builtin_va_arg(v[1], int);
   }

   __builtin_va_end(v[0]);
   __builtin_va_end(v[1]);
	 free(v);

   return result;
}

int main() {
  int x = doubleSum(3, 1,2,3);
  //@ assert x == 12;
}
