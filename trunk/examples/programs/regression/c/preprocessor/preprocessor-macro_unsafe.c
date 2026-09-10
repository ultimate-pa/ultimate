//#Unsafe
/*-----------------------------------------------------------------------------
 * C program with preprocessor macro to test macro parsing and substitution
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 2023-09-25
 *---------------------------------------------------------------------------*/

#define VALUE 100

int main(void)
{
    int ret = VALUE;
    //@ assert(ret == 200);
    return ret;
}
