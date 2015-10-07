#include <stdlib.h>

int main()
{
    int* i = alloca(sizeof(int));
    int* j = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *c = 0;
    for (*i = 0; *i < 100; (*i)++) *c = *c + 1;
    for (*j = 5; *j < 21; *j += 3) *c = *c + 1;
    return *c;
}