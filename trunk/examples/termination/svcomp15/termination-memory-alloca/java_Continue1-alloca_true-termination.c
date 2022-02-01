#include <stdlib.h>

int main()
{
    int* i = alloca(sizeof(int));
    int* c= alloca(sizeof(int));
    *i = 0;
    *c = 0;
    while (*i < 20) {
        (*i)++;
        if (*i <= 10) continue;
        (*c)++;
    }
    return *c;
}