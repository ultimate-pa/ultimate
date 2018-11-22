//#Safe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
#include<stdlib.h>
int main() {
  // initialization (long long, so it does not fit into one int and needs
  // several writes (atleast in 32bit model))
  long long a[3] = { 1 };

  // just so there are two heap arrays
  int * * p = malloc(sizeof(int *));
  **p = 5;

  /* These assertions hold, since the first value is explicitly initialized to
   * 1 and the rest is filled with 0s. */
  if (a[0] != 1) {
    //@ assert \false;
  }
  if (a[1] != 0) {
    //@ assert \false;
  }
  if (a[2] != 0) {
    //@ assert \false;
  }
}
