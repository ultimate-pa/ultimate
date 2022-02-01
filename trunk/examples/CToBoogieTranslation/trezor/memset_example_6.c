#include <stdint.h>

typedef unsigned char uint8_t;

static uint8_t _oledbuffer[1024];

int main()
{
  for(int i = 0; i < 1024; i++)
  {
    _oledbuffer[i] = 0;
  }
  return 0;
}
