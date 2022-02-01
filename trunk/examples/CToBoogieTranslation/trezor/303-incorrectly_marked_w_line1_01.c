#include <stdint.h>

// Ultimate needs this
typedef unsigned int uint32_t;

int main(void)
{
  uint32_t data = (*(volatile uint32_t *)(0x50000000U));
  return 0;
}
