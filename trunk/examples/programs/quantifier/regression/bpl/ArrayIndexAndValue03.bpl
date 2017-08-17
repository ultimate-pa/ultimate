//#Safe
/* Date: 2017-07-30
 * Author: heizmann@informatik.uni-freiburg.de
 * Similar than ArrayIndexAndValue02 but for WP-based computation.
 */
var a : [int] int;
var k : int;
var i : int;

procedure ULTIMATE.start() returns();
modifies a, k;

implementation ULTIMATE.start() returns()
{

  assume (i == k);
  assert (a[k] == 23 || a[i] != 23);  
}
