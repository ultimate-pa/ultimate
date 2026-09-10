//#Unafe
/*-----------------------------------------------------------------------------
 * C program with preprocessor macros to test macro parsing and substitution
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 2023-09-25
 *---------------------------------------------------------------------------*/

#define SELECT_FUNC_ONE

#define VALUE 100

int compute_one(int num)
{
    return num - VALUE;
}

int compute_two(int num)
{
    return num + VALUE;
}

#ifdef SELECT_FUNC_ONE
#define FUNC(VAL) compute_one(VAL)
#else
#define FUNC(VAL) compute_two(VAL)
#endif

int main(void)
{
    int ret = FUNC(VALUE);
    //@ assert(ret == 100 + 100);
    return ret;
}
