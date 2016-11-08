#include <stdlib.h>

int main() {
    int* x1 = alloca(sizeof(int));
    int* x2 = alloca(sizeof(int));
    while (*x1 <= 10) {
        *x2 = 1000;
        while (*x2 > 1) {
            *x2 = *x2 - 1;
        }
        *x1 = *x1 + 1;
    }
}