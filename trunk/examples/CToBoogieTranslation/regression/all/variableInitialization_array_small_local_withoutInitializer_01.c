//#Unsafe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
int main() {
  // no initialization
  int a[3];

  /* This assertion can be violated since the values of the array are
   * indeterminate. */
  if (a[0] != 0) {
    //@ assert \false;
  }
}
