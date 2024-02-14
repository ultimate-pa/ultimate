// #Safe
/*
 * Date: 2024-02-06
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

//@ ensures \result >= x;
int f(int x);

int main() {
  int r = f(0);
  //@ assert r >= 0;
}
