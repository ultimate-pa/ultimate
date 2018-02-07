//#Safe
/*
 * basic test to check how multidimensional arrays are handled by the translation
 */
int main() {
  int a[2][3];

  a[1][2] = 7;

  int x;
  x = a[1][2];

  //@ assert x == 7;
}
