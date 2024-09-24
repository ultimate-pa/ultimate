// #Safe
/*
 * Date: 2024-01-31
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

//@ requires x == 0;
int f(int x);

int main() {
  int r = f(0);
  //@ assert r == 1;
}

//@ requires x >= 0;
//@ ensures \result == x+1;
int f(int x) {
  return x+1;
}