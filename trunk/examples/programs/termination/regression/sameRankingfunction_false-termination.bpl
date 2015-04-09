//#nonterminating
/*
 * Date: 10.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y: int;

procedure main()
modifies x, y;
{
  assume true;
  while (x > 0) {
    if (*) {
      x := x - 55;
    } else if (*) {
      x := x - 2;
    } else if (*) {
      x := x - 3;
    } else {
      // do nothing
    } 
  }
}