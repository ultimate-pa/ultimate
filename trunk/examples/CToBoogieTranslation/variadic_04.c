//#Safe
/*
Example for extern variadic function

2018-10-12 DD 
*/

extern int add_nums(int count, ...);

int g; 

int foo(){
    g = g + 1;
}

int main(void) 
{
    int result;
    result = add_nums(5, 1, 2, foo(), 4, 5);
    //@assert g == 1;
    return 0;
}