////#Safe
/*
 * 
 *
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
