////#Safe
/*
 *
 * author: nutz
 * date: 2014-11-25
 */

#include<stddef.h>

int main() {
  int x = 10;
  while (x-- > 0) {
    continue;
  }
  //@assert x == -1;

  return 0;
}
