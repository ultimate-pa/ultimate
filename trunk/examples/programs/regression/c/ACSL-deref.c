// #Safe
/*
 * Test for pointer dereference in ACSL expressions
 * 
 * Date: 2023-09-21
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int* x = malloc(sizeof(int));
  *x = 0;
  //@ assert *x == 0;
}