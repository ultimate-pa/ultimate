//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */

int main() {
  int * p;
  // speciality here: size of compound literal depends on size of initializer
  p = (int [3]) { 1, 2, 3 };

  if (p[0] != 1) {
  	//@ assert \false;
  }
  if (p[1] != 2) {
  	//@ assert \false;
  }
  if (p[2] != 3) {
  	//@ assert \false;
  }
}
