unsigned f() {
  if (__VERIFIER_nondet_int()) return 0;
  return f() + 1;
}

int main(){
  if (f() == 2) reach_error();
}