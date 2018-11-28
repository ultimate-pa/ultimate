//#Safe
/*
 * Should test the functionality that chooses when to use constant arrays during
 * initialization.
 */
int x;
int y;
int * a[1000] = { &x, &y };

int main() {
  if (a[0] != &x) {
    //@ assert \false;
  }
  if (a[1] != &y) {
    //@ assert \false;
  }
  if (a[500] != 0) {
    //@ assert \false;
  }
  if (a[999] != 0) {
    //@ assert \false;
  }
}
