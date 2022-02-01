/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * 'p-1' has not the right type during translation.
 */

#include <stdlib.h>

int main()
{
    int* p;
    p = malloc(3 * sizeof(*p));
    free(p-1);

    return 0;
}
