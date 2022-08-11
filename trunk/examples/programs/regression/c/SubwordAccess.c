//#Unsafe
/*  
 * Date: 2021-10-12
 * 
 * Reveals that the an adaption of the memory model's resolution is not only 
 * necessary if a pointer cast increases the size of the type but also if
 * it reduces the size of the type.
 * 
 */

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
