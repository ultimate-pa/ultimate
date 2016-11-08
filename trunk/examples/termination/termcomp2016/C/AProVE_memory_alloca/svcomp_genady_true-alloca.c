#include <stdlib.h>

int main() {
    int* i = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    *j = 1;
    for (*i = 10000; *i - *j >= 1; (*i)--) {
        (*j)++;
    }
}