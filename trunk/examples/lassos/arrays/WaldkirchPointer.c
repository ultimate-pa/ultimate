#include <stdlib.h>

int main()
{
    int* x = malloc(sizeof(int));
    while (*x >= 0) {
         (*x)--;
    }
    return 0;
}