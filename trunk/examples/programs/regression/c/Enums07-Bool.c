//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-03-05
// We represent the negation internally as a Boolean and fail to convert it back.

#include <stdio.h>

enum
{
  nonZero = 23,
  zero = 0,
};

enum
{
  alpha = !zero,
  beta = !nonZero,
};

int main() {
    printf("%d\n",alpha);
    printf("%d\n",beta);
    //@ assert alpha == 1;
    //@ assert beta == 0;
    return 0;
}
