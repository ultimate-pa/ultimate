#include <stdlib.h>

int main() {
    int* x = alloca(sizeof(int));
    while (*x <= 10) {
        if (*x > 6) {
            *x = *x + 2;
        }
    }
}