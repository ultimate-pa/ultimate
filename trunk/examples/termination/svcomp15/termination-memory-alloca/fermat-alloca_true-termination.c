#include <stdlib.h>

int main()
{
    int* MAX = alloca(sizeof(int));
    int* a = alloca(sizeof(int));
    int* b = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *MAX = 1000;
    *a = 1;
    *b = 1;
    *c = 1;
    while (1) {
        if ((((*a)*(*a)*(*a)) == (((*b)*(*b)*(*b)) + ((*c)*(*c)*(*c))))) {
            return 1;
        }
        (*a)++;
        if (*a > *MAX) {
            *a = 1;
            (*b)++;
        }
        if (*b > *MAX) {
            *b = 1;
            (*c)++;
        }
        if (*c > *MAX) {
            break;
        }
    }
    return 0;
}
