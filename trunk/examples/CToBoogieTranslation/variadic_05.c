//#Safe
/*
Example for a variadic function that does not use its variadic argument.

2018-10-08 DD 
*/

#include <stdarg.h>
 
int add_nums(int count, ...) 
{
    int result = 0;
    return result;
}

int main(void) 
{
    int result;
    result = add_nums(10,11,12);
    //@assert result == 0;
}