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

int foo(int x){
    if(x != 5){
        //@assert \false;
    }
    return x;
}

int main(void) 
{
    int result;
    int x = 2;
    int y = 3;
    
    result = add_nums(10,foo(x+y),x*y);
    //@assert result == 0;
}