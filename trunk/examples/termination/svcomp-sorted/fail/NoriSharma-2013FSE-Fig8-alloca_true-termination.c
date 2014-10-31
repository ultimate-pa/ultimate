#include <stdlib.h>

int main() {
    int* u = alloca(sizeof(int));
    int* x = alloca(sizeof(int));
    int* v = alloca(sizeof(int));
    int* y = alloca(sizeof(int));
    int* w = alloca(sizeof(int));
    int* z = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *u = *x;
    *v = *y;
    *w = *z;
    *c = 0;
    
    while (*x >= *y) {
        *c = *c + 1;
        if (*z > 1) {
            *z = *z - 1;
            *x = *x + *z;
        } else {
            *y = *y + 1;
        }
    }
}