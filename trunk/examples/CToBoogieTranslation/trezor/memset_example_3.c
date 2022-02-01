#include <stdint.h>
// memset definition to satisfy gcc --pedantic
#include <string.h>

typedef unsigned char uint8_t;

static uint8_t _oledbuffer[1024];

int main()
{
  memset(_oledbuffer, 0, 1);
  return 0;
}
