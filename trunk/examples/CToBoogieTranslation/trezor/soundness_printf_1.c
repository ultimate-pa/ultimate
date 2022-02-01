#include <stdio.h>
#include <stdint.h>
// Ultimate needs this
typedef unsigned char uint8_t;

uint8_t data[1];

int main(void)
{
    data[0] = 42;
    printf("valid access: %u\n", data[0]);
    // this will be ignored by Ultimate
    printf("out of bounds read: %u\n", data[-1]);
    return 0;
}
