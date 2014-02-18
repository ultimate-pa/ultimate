//#rTerminationDerivable
/*
 * Lasso program depicted in Figure 7 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(offset, i, a_i, a.length)=a.length-i
 * with linear supporting invariant offset>=1.
 * 
 * Occured as abstration of the following program with an array that contains
 * arbitrary positive values.
 * 
 * offset := 1; i := 0;
 * while (i <= a.length) {
 *   i := i + offset + a[i];    
 * }
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var offset, i, a_i, a.length: int;
  offset := 1;
  i := 0;
  while (i <= a.length) {
    havoc a_i;
    assume (a_i >= 0);
    i := i + offset + a_i;    
  }
}

