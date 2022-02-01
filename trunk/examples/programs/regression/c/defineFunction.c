//#Unsafe
/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * '#define' declares the function '___MY_ASSERT'.
 * This is not supported.
 * 
 * NOTE: I am not sure what causes the error, some
 */
void fail() {
	//@ assert \false;
}

#define ___MY_ASSERT(cond) do {     \
    if (!(cond))                    \
        fail();                     \
} while (0)

int main() {
    ___MY_ASSERT(0);
    
    return 0;
}
