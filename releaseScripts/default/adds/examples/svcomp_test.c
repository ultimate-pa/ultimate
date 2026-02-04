//#Safe

extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  int r = 0;
  for (int i=0; i<n; i++) {
    r++;
  }
  if (r < n) reach_error();
}
