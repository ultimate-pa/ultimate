//#Safe
/* Simplest program that I could imagine that is
 * - recursive but not tail recursive
 * - terminating
 * - and there is no bound for the longest execution.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 31.1.2014
 *
 */

procedure rec(n: int) returns ();

implementation rec(n: int) returns ()
{
  if (n >= 0) {
      call rec(n-1);
      call rec(n+1-2);
  }
}

