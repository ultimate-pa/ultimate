extern void __VERIFIER_error();

void f(int);
void f2(int);

void f(int n) {
  if (n<3) return;
  n--;
  f2(n);
  ERROR: __VERIFIER_error();
}

void f2(int n) {
  if (n<3) return;
  n--;
  f(n);
  ERROR: __VERIFIER_error();
}

int main(void) {
  f(4);
}
