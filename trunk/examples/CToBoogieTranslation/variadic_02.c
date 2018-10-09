//#Safe
/*
Example for variadic functions adapted from https://en.cppreference.com/w/c/variadic/va_start

2018-10-08 DD 
*/

#include <stdarg.h>
 
int add_nums(int count, ...) 
{
    int result = 0;
    va_list args;
    va_start(args, count);
    for (int i = 0; i < count; ++i) {
        result += va_arg(args, int);
    }
    va_end(args);
    return result;
}
 
int main(void) 
{
    int result;
    result = add_nums(5, 1, 2, 3, 4, 5);
    //@assert result == 15;
}