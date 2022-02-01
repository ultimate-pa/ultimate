//#Safe
/*
 * Tests using array initializers with designators.
 */
#include<stdio.h>
int main() {
  // initialization
  int a[3] = { [2] = 3, [1] = 2, [0] = 1 };

  printf("a[0]: %i\n", a[0]);
  printf("a[1]: %i\n", a[1]);
  printf("a[2]: %i\n", a[2]);

  /* These assertions hold, since the first value is explicitly initialized to
   * 1 and the rest is filled with 0s. */
  if (a[0] != 1) {
    //@ assert \false;
  }
  if (a[1] != 2) {
    //@ assert \false;
  }
  if (a[2] != 3) {
    //@ assert \false;
  }
}
