//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-08-03
*/

void positive(int count,...) {
  __builtin_va_list valist;
  __builtin_va_start(valist, count);
  for (int i=0; i<count; i++) {
    int elem = __builtin_va_arg(valist, int);
    //@ assert elem > 0;
  }
  __builtin_va_end(valist);
}

int main() {
  positive(2, 'a', 42);
}