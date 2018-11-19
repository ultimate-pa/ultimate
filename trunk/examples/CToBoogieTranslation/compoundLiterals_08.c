//#Unsafe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
int * foo() {
  return & (int) { -1 };
}

int main() {
  int * res1;
  int * res2;
  res1 = foo();
  // memory unsafe, because the compound literal is out of scope
  if (*res1 != -1) {
    //@ assert \false;
  }
  
}
