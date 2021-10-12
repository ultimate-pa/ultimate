//#Unsafe

#include <stdio.h>

int main() {
  int x = 0;

  char* ptr = (char*)&x;
  ptr[1] = (char)1;

  if (x == 0) {
    printf("ZERO: correct\n");
  } else {
    printf("%d: incorrect\n", x);
  }

  // violated assertion:
  //@ assert x == 0;
}
