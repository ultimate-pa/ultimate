////#Safe
/*
 * 
 *
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>

int main() {

   int a[2] = { 3 }, *p;

   p = (int *) a;

   if (*p != 3) {
     //@ assert \false;
   }

   return 0;
}
