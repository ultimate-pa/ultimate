//#Safe
/* Date: 2017-07-30
 * Author: heizmann@informatik.uni-freiburg.de
 */
var a : [int] int;
var k : int;
var i : int;

procedure ULTIMATE.start() returns();
modifies a, k;

implementation ULTIMATE.start() returns()
{

  assume a[k] == 23;
  assume a[i] != 23;
  assert (i != k);
  
}
