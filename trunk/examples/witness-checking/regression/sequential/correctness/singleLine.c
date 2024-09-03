int main() {
  int n = 3;
  int x = 0; for (int i=0; i<n; i++) x++; for (int i=0; i<n; i++) x--;
  //@ assert x == 0;
}