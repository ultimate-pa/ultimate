
//#Unsafe
/*
 * Simple program to compare the effect of various "stop after first violation" behaviors. 
 * Variant "Restart the analysis" requires ~7s and 31 iterations per assertion for assertions in L24 and L26. 
 *
 * Date: 2021-06-24
 * Author: dietsch@informatik.uni-freiburg.de
 * 
 */

/*
    Strategy CAMEL
    1. [x] Restart CEGAR for each error location, [ ] Stop after first violation was found, Error locations removal mode SIMPLE_ERROR_AUTOMATON
        CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 31953.0ms
        CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 29404.0ms, 
        CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 1659.5ms,
    2. [ ] Restart CEGAR for each error location, [ ] Stop after first violation was found, Error locations removal mode SIMPLE_ERROR_AUTOMATON
        CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 28342.8ms
 */


procedure main()
{
  var x,N : int;
  N:=30;
  x:=0;
  
  
  while(x<N){
      x:=x+1;
  }
  
  if (*){
    assert false;
  } else if (*){
    assert false;
  } else if (*){
    assert x == N;
  }
}
