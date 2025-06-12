//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2025-04-30
*/

#include <stdarg.h>

void positive(int count,...) {
  va_list valist;
  va_start(valist, count);
  for (int i=0; i<count; i++) {
    int elem = va_arg(valist, int);
    //@ assert elem > 0;
  }
  va_end(valist);
}

int main() {
  positive(2, 'a', 42);
}