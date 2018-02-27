#include <stdint.h>

typedef unsigned char uint8_t;

static uint8_t _oledbuffer[1024];

int main()
{
  _oledbuffer[-1] = 0;
  return 0;
}
