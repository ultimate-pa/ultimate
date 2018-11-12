//#Unsafe
#include<stdio.h>
int main() {
  struct structtype {
    int i1;
    int i2;
  };

  struct structtype s = { .i2 = 3, .i1 = 7 };

  printf("i1: %i\n", s.i1);
  printf("i2: %i\n", s.i2);

  //@ assert s.i1 == 3;
  //@ assert s.i2 == 7;
}
