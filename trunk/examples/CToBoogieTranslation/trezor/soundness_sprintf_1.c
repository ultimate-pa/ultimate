// source: http://www.cplusplus.com/reference/cstdio/sprintf/
/* sprintf example */
#include <stdio.h>

int main ()
{
  char buffer[100];
  int data[1];
  data[0] = 42;

  // this is valid
  sprintf(buffer, "%d", data[0]);
  // out of bounds read (upper)
  sprintf(buffer, "%d", data[1]);
  // out of bounds read (lower)
  sprintf(buffer, "%d", data[-1]);
  return 0;
}
