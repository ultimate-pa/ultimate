//#Unsafe
#include <stdio.h>

int main() {
  int x = 42;

  int y = printf("%d is the answer to life, the universe, and everything!", x);

  //@ assert y == 42;
}
