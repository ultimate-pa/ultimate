//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 *
 * example from C11 6.5.2.5.1
 */
int * p = (int [2]) { 2, 4 };

int main() {
  if (p[0] != 2) {
    //@ assert \false;
  }
  if (p[1] != 4) {
    //@ assert \false;
  }
}
