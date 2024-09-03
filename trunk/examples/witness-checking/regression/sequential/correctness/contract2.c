int f(int x) {
  //@ assert x > 0;
  return x-1;
}

int main() {
  int x = __VERIFIER_nondet_int();
  if (x <= 0) return;
  int r = f(x);
  //@ assert r >= 0;
}
