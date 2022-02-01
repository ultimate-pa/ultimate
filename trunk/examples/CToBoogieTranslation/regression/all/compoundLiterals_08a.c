//#Unsafe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
struct stu {
  int i1;
  int i2;
  int i3;
};


struct stu * foo() {
  return & (struct stu) { -1, -2, -3 };
}

int main() {
  struct stu * res1;
  res1 = foo();
  // memory unsafe, because the compound literal is out of scope
  if ((*res1).i1 != -1) {
    //@ assert \false;
  }
}
