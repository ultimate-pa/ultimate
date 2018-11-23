//#Safe
/*
 * Test calloc functionality
 */
#include<stdio.h> 
#include<stdlib.h> 
int main() {
  int *p = calloc(5, sizeof(int));

  printf("* p     : %d\n", *p);
  printf("*(p + 1): %d\n", *(p + 1));
  printf("*(p + 2): %d\n", *(p + 2));
  printf("*(p + 3): %d\n", *(p + 3));
  printf("*(p + 4): %d\n", *(p + 4));

  if (*p != 0) {
    //@ assert \false;
  }
  if (*(p + 1) != 0) {
    //@ assert \false;
  }
  if (*(p + 2) != 0) {
    //@ assert \false;
  }
  if (*(p + 3) != 0) {
    //@ assert \false;
  }
  if (*(p + 4) != 0) {
    //@ assert \false;
  }
}
