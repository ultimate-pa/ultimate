extern int __VERIFIER_nondet_int(void);

int iterate(int bound) {
  int i;
  int sum = 0;
  for(i=0; i<bound; i++) {
    sum += i;
  }
  return sum;
}

int main() {
    return iterate(__VERIFIER_nondet_int());
}
