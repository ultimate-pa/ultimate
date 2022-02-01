//#Safe
/**
 * Test support of the standard libary function realloc.
 */
#include<stdlib.h>
int main() {

  struct stu {
    int i1;
    int i2;
  };

  struct stu *ps = malloc(sizeof(struct stu));

  ps->i1 = 3;
  
  int *pi = realloc(ps, sizeof(int));

  if (*pi != 3) {
    //@ assert \false;
  }
  free(pi);
}
