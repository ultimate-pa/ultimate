#include <stdlib.h>

int main() {
    int* a = alloca(sizeof(int));
    int* i = alloca(sizeof(int));
    int* b = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    int* M = alloca(sizeof(int));
    int* N = alloca(sizeof(int));
    *a = *i;
    *b = *j;
    *c = 0;
    
    while (*i < *M || *j < *N) {
        *i = *i + 1;
        *j = *j + 1;
        *c = *c + 1;
    }
}