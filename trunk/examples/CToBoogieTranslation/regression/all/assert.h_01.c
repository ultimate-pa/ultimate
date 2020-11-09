//#Unsafe
/*
    Example for preprocessed assert from assert.h in SV-COMP 2021
    
    Adapted from test_locks_9.c
    
    2020-10-19 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
*/
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "test_locks_9.c", 3, "reach_error"); }

int main()
{
  int x = 0;
  if (x != 1) goto ERROR; 
  
  out:
     return 0;
  ERROR: {reach_error();abort();}
     return 0;
}