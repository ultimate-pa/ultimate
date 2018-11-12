////#Unsafe
/*
 *
 * author: nutz
 * date: 2014-11-25
 */

#include<stddef.h>

int main() {

  char x = 0;
  for (int i = 0; i < 8; ++i) 
   x |= 1 << i;
  //@assert(x > 0); 

  return 0;
}
