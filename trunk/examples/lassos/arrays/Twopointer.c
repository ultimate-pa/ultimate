#include <stdlib.h>

int main()
{
    int* x = malloc(sizeof(int));
    int* y = malloc(sizeof(int));
    while (1) {
         if (*x < 0) break;
         (*x)--;
         (*y)++;
    }
    return 0;
}