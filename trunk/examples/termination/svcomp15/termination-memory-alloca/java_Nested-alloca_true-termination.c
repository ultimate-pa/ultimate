#include <stdlib.h>

int main()
{
    int* i = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *c = 0;
    for (*i = 0; *i < 10; (*i)++) {
        for (*j = 3; *j < 12; *j += 2) {
            *j -= 1;
            *c += 1;
        }
    }
    return *c;
}