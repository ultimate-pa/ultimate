#include <stdint.h>

typedef unsigned int uint32_t;

uint32_t __stack_chk_guard;

uint32_t random32(void)
{
  // xkcd classic
  return 4;
}

int main(void)
{
  __stack_chk_guard = random32();
}
