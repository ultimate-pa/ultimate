//#Unsafe
/*
    Example for preprocessed assert from assert.h in SV-COMP 2021
    
    Adapted from test_locks_9.c
    
    2020-10-19 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
*/
#include <assert.h>
extern void abort(void);
void reach_error() { assert(0); }

int main()
{
  int x = 0;
  if (x != 1) goto ERROR; 
  
  out:
     return 0;
  ERROR: {reach_error();abort();}
     return 0;
}