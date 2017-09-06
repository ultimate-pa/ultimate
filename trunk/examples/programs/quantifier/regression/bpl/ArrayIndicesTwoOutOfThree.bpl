//#Safe
/* Date: 2017-08-07
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Only two but not all three indices can be equivalent.
 * 
 */
var a : [int] int;
var k : int;
var i : int;
var j : int;

procedure ULTIMATE.start() returns();
modifies a, k;

implementation ULTIMATE.start() returns()
{
  assume (a[i] == 23);
  assume (a[j] == 23);
  assume (a[k] == 23);
  assume ( (i-j)*(i-j)+(j-k)*(j-k) > 0);
  a[j] := 42;
  assert (a[i] == 23 || a[k] == 23);  
}
