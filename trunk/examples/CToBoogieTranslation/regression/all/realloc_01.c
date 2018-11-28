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

  int *pi = malloc(sizeof(int));

  *pi = 3;
  
  struct stu *ps = realloc(pi, sizeof(struct stu));

  if (ps->i1 != 3) {
    //@ assert \false;
  }
  free(ps);
}
