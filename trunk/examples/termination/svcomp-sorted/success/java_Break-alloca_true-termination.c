#include <stdlib.h>

int main()
{
    int* i = alloca(sizeof(int));
    int* c= alloca(sizeof(int));
    *i = 0;
    *c = 0;
    while (1) {
        if (*i > 10) break;
        (*i)++;
        (*c)++;
    }
    return *c;
}