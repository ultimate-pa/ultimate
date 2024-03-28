//#rNonTermination
/* Simple example with Zeno behavior (example does not use division).
 * (See Wellington.bpl for a modification of this lasso
 * that uses int instead of real).
 *
 * Date: 23.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Loop given by the following constraints.
 * 1: a >= 0
 * 2: b' > 0
 * 3: a' = a - b'
 * 
 * If we try find some x,y,\lamda such that
 * (x,x+y)\in Loop and (y,\lambda*y)\in Loop, 
 * we fail for any \lambda.
 * 
 */

procedure main() returns ()
{
  var a, b: real;
  assume(true);
  while (a >= 0.0) {
    havoc b;
    assume b > 0.0;
    a := a - b;
  }
}

