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
  
  a = a >> 65;
  
  x = x << z;
  y = x << z;
  if (x != y) {reach_error();abort();}
  
  return 0;
}