//#Safe
/**
 * Test support of the standard libary function realloc.
 */
#include<stdlib.h>
int main() {

  struct stu {
    int * i1;
    int * i2;
  };

  int *pi = malloc(sizeof(int));
  int **ppi = malloc(sizeof(int *));
  *ppi = pi;

  *pi = 3;
  
  struct stu *pps = realloc(ppi, sizeof(struct stu));

  if (*(pps->i1) != 3) {
    //@ assert \false;
  }
  free(pps);
  free(pi);
}
