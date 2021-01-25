//#Unsafe
/*
    Overapproximation of functions not even congruent
    
    Adapted from test_locks_9.c
    
    2020-10-19 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
*/

extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "", 3, "reach_error"); }

int main()
{
  unsigned int x = 0;
  unsigned int z = 1;
  unsigned int y = 1;
  int a = 0;
  
  a = a >> 65; // even with overflow checks, no check for negative a (6.5.7.5 C11) 
  a = a << 65; // no assume in non-overflow setting , but perhaps not necessary 
  a = a >> 100000; // large constants take a long time to write/compute (make it larger to see how long it takes to compute the string for 2^1000000)
  
  x = x << z;
  y = x << z;
  if (x != y) {reach_error();abort();}
  
  return 0;
}