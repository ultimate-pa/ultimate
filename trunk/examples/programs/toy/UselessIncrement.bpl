//#Unsafe
/* Date: July 2010
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * The program is incorrect with respect to its specification.
 * 
 */

procedure UselessIncrement(n: int) returns (z: int);
requires n>=0;
ensures z != 23;

implementation UselessIncrement(n: int) returns (z:int)
{
  var i, x, y: int;
  x := 0;
  i := n;
  while(i != 0) {
    x := x + 1;
    i := i - 1;
  }
  y := 0;
  while(*) {
    y := y + 1;
  }
  i := n;
  while(i != 0) {
    x := x - 1;
    i := i - 1;
  }
  z := x + y;
}

