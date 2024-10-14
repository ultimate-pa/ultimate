unsigned sum(unsigned n) {
  if (n == 0) return 0;
  return sum(n-1)+n;
}

int main(){
  unsigned x = __VERIFIER_nondet_uint();
  if (sum(x) != x) reach_error();
}