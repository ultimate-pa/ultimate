#include "hdr_a.h"

int main()
{
  // Without resolving includes correctly c() could return either 2303
  // or 4711.
  int d = c();
  //@assert d == 2303;
  return 0;
}
