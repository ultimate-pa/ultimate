int global;

int f() {
  return global++;
}

int main() {
  global = 5;
  int r = f();
  //@ assert r == 5 && global > 5;
}
