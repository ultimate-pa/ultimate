#include <stdlib.h>

int main() {
    int* x = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    // continue only for values where there won't be any overflow or underflow
    // on systems where sizeof(int)=4 holds.
    if (*x > 10000 || *x < -10000 || *y > 10000 || *z > 10000) {
        return 0;
    }
    while (*y >= 1) {
        (*x)--;
        while (*y < *z) {
            (*x)++;
            (*z)--;
        }
        *y = *x + *y;
    }
    return 0;
}