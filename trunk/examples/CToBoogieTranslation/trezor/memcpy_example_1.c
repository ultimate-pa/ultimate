#include <stdint.h>
// memcpy definition to satisfy gcc --pedantic
#include <string.h>

typedef unsigned char uint8_t;

static uint8_t _oledbuffer[1024];

int main()
{
  memcpy(_oledbuffer, "42", 2);
  return 0;
}
