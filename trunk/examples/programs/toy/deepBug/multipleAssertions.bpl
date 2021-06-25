
//#Unsafe
/*
 * Simple program to compare the effect of various "stop after first violation" behaviors. 
 * Variant "Restart the analysis" requires ~7s and 31 iterations per assertion for assertions in L24 and L26. 
 *
 * Date: 2021-06-24
 * Author: dietsch@informatik.uni-freiburg.de
 * 
 */

// Variant "1 Cegar, ERROR_AUTOMATON": CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 12395.4ms, OverallIterations: 34, 
// Variant "1 Cegar, Stop after violation": CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 9311.1ms, OverallIterations: 32
// Variant "3 Cegar, Do not stop after violation": 
// CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 7631.7ms, OverallIterations: 31
// CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 7616.6ms, OverallIterations: 31
// CFG has 1 procedures, 7 locations, 3 error locations. Started 1 CEGAR loops. OverallTime: 8968.8ms, OverallIterations: 32


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
