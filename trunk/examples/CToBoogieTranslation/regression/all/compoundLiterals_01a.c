//#Safe
/*
 * Test compound literals (e.g. "(int) { -1 }", see also C11 6.5.2.5).
 */
int foo(int i) {
  return i;
}

int bar() {
  int x = -1;
  return foo((int) { x });
}

int main() {
  int res;
  res = bar();
  //@ assert res == -1;
}
