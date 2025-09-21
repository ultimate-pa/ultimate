// #Safe
/*
 * Date: 2025-01-07
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  float x = 1.57;
  float* p = &x;
  //@ assert *p > 0;
}
