//#Safe
/* Date: 2015-04-28
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Program depicted in Figure 4 of the following paper.
 * 2007PLDI - Beyer,Henzinger,Majumdar,Rybalchenko - Path Invariants
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  x := 0; y := 50;
  while (x < 100) {
    if (x < 50) {
      x := x + 1;
    } else {
      x := x + 1;
      y := y + 1;
    }
}
//  assert(y >= 100 && y < 100);
    assert(y >= 100);
    assert(y <= 100);
}


