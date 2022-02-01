/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Syntax Error in SvCompHandler:
 * (type instanceof CArray)
 */
int main ()
{
    int arr[2];
    int *bound;
    *bound = sizeof(*arr);
    return 0;
}
