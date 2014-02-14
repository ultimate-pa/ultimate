/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * 'sizeof' is not supported for pointers.
 */
int main () {
    int array[1];
    int *bound = array + sizeof(array)/sizeof(*array) - 1;

    return 0;
}
