//#Safe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
int a[3];

int main() {
  /* These assertions hold since all value are implicitly initialized to 0. */
  if (a[0] != 0) {
    //@ assert \false;
  }
  if (a[1] != 0) {
    //@ assert \false;
  }
  if (a[2] != 0) {
    //@ assert \false;
  }
}
