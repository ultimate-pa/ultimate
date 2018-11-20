//#Safe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
// implicit initialization
int a[1000];

int main() {
  /* These assertions hold since all value are implicitly initialized to 0. */
  if (a[0] != 0) {
    //@ assert \false;
  }
  if (a[1] != 0) {
    //@ assert \false;
  }
  if (a[500] != 0) {
    //@ assert \false;
  }
  if (a[999] != 0) {
    //@ assert \false;
  }
}
