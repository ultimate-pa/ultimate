////#Safe
/*
 * Case: We have an extern declaration with no inparams, then a call of that function with inparams
 * --> we do a boogie declaration according to the call..
 * author: nutz
 */

#include<stddef.h>

extern int f();

int main() {
  f(0, 2);
  return 0;
}
