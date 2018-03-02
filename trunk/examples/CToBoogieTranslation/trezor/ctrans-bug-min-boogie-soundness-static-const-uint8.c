//#Unsafe
#include <stdint.h>

typedef unsigned char uint8_t;

static const uint8_t * const pubkey[1] = {
 (const uint8_t *)"\x42",
};

int main() {
    // out of bounds access which is missed by Ultimate
    return pubkey[0][2];
}
