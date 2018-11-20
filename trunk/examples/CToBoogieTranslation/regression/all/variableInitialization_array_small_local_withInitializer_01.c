//#Safe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
int main() {
  // initialization
  int a[3] = { 1 };

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
