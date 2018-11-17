//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
int foo(int i) {
  return i;
}

int bar() {
  return foo((int) { -1 });
}

int main() {
  int res;
  res = bar();
  //@ assert res == -1;
}
