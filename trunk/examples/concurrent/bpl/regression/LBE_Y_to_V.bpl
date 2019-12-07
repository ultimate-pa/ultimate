//#Safe
/*
 * A program that demonstrates when a "Y to V" check can be applied.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-10-24
 * 
 */

var x : int;
var y : int;

procedure ULTIMATE.start();
modifies x;
modifies y;

implementation ULTIMATE.start()
{
  x := 1;
  if (x > 0) {
    x := x + 1;
  } else {
    x := x - 1;
  }
  x := 2;
}

procedure foo();
modifies y;

implementation foo()
{
  y := 2;
}