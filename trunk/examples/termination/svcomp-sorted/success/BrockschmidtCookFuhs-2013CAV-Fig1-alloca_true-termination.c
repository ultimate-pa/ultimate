#include <stdlib.h>

int main() {
    int* i = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    int* n = alloca(sizeof(int));
    while (*i < *n) {
        *j = 0;
        while (*j <= *i) {
            *j = *j + 1;
        }
        *i = *i + 1;
    }
    return 0;
}