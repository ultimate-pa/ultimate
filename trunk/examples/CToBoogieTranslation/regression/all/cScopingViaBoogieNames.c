////#Safe
/*
 *
 * author: nutz
 * date: 2014-11-25
 */

#include<stddef.h>

int main() {

  int x = 0;

  while (x++ < 10) {
  { 
     int y; 
     y++;
  }
   int y;
   y = x++;
  }

  //@ assert x == 10;

  return 0;
}
