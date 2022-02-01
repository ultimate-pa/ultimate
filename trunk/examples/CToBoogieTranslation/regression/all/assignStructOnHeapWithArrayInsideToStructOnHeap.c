////#Safe
/*
 * author: nutz
 * date: 2014-10-14
 */

#include<stddef.h>

int main() {
  struct s {
    int a[2];
    char b;
  } si, sj;

  (si.a)[0] = 3;
  (si.a)[1] = 8;

  sj = si;

  int i = (sj.a)[0];
  int j = (sj.a)[1];
  
  //@ assert i == 3;
  //@ assert j == 8;

  &si;
  &sj;

  return 0;
}
