////#Safe
/* Test file that requires treatment of function pointers which are actually used in
 * a function call.
 * author: nutz
 */

#include<stddef.h>

int zero() {
  return 1;
}

int one(int i) {
  return 2;
}

int one1(int i) {
  return i;
}

int one2(int i) {
  return i + 1;
}

int two(int i1, int i2) {
  return 3;
}

int two1(int i1, int i2) {
  return i1 + i2;
}

int main() {

  int (*toZero)() = &zero;
  int z = (*toZero)();
  toZero = zero;
  z = toZero();

  int (*toOne)(int) = &one;
  z = (*toOne)(1);
  toOne = &one1;
  z = (*toOne)(1);
  toOne = &one2;

  int (*toTwo)(int, int) = &two;
  z = (*toTwo)(1, 2);

  return 0;
}
