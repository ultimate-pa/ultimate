//
// regression test (5.01.2016)
//
#include <stdlib.h>
#include <string.h>

int main() {
  int *jp = malloc(3 * sizeof(int) + 1);

  *jp = 4;

  jp++;

  memset(jp, 12345, 2 * sizeof(int));
}
