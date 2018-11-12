////#Safe
/*
 *
 * author: nutz
 * date: 2014-11-25
 */

#include<stddef.h>

int main() {

  int x = 0;
  int y = 0;

  int z;

  z = x + y - y * x;

  x++;
  ++x;
  x--;
  --x;

  return 0;
}
