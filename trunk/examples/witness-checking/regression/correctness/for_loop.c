void main() {
  int x = 0;
  for (int i=0; i<=3; i++) {
    x += i;
  }
  if (x != 6) {
    reach_error();
  }
}