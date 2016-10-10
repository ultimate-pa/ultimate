/*
 * Test if the cast from double to int is translated correctly. We need to round down. 
 * Currently (15.5.2015), the translation works, but with a function without specification.
 * (Thus we can translate this, but the resulting Boogie program is unsafe.)
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>

int main() {
  double d = -1.1;
  int i = (int) d;
  //@assert i == 1;
  return 0;
}
