/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Array initialization is not supported.
 * Neither line works, but there is a different error.
 */
int main(int argc, char **argv) {
    int array1[2] = { 1 };
    static int array2[2] = { 1 };
    
    return 0;
}
