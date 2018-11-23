//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
struct stu {
  int i1;
  int i2;
};

int foo(struct stu s) {
  return s.i2;
}

int bar() {
  return foo((struct stu) { -1, -2 });
}

int main() {
  int res;
  res = bar();
  //@ assert res == -2;
}
