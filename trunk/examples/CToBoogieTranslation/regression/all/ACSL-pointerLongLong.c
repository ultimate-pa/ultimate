// #Safe
/*
 * Date: 2025-01-07
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  long long x = 32;
  long long* p = &x;
  //@ assert *p == 32;
}
