//#Safe
/*
 * Bug in parallel composition in r8308.
 * y occured unneccessarily as inVar which might lead to problems in following
 * compositions.
 * 
 * Date: 09.02.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 *
 */

var x : int;
var y : int;

procedure method1() returns ()
modifies x,y;
{
  if (y != 0) {
    if (x != 0) {
      y := 1;
    } else {
      y := 0;
    }
  } 
}


