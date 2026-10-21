//#Safe
/*
 * Date: 2026-10-21
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 */

struct S {
 int n;
};
struct S s[100000];

int main() {
  s[0].n = 10;
  if (s[0].n != 10) reach_error();
}
