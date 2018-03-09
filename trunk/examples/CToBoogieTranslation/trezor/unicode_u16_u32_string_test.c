//#Safe
#include <uchar.h>

typedef short unsigned int char16_t;
typedef unsigned int char32_t;

int main(void) {
    char16_t c16 = u'\u00F6';
    char32_t c32 = U'\U0010FFFF';
}
