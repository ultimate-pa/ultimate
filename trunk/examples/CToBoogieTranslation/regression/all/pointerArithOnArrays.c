////#Safe
/*
 * 
 *
 * author: nutz
 * date: 2014-10-16
 */

#include<stddef.h>


int main() {
  struct s {
    int a[2], i;
  } *si;

  si = (struct s *)(si->a + si->i);

  return 0;
}
