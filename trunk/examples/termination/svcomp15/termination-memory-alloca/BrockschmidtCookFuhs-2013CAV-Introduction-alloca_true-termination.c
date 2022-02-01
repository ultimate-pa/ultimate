#include <stdlib.h>

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    *y = 1;
    while (*x > 0) {
        *x = *x - *y;
        *y = *y + 1;
    }
    return 0;
}