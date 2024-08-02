//#Safe
/*
 * Luxembourg-WithArrays transformed to integer program.
 * The loop invariant (x > y && 1000-a_y>=a_x) allows us to prove correctness.
 * 
 * Date: 2016-04-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  var a_x, a_y: int;
  
  assume x > y;
  a_x := 0;
  if (x == y) {
    a_y := 0;
  }
  a_y := 1000;
  if (y == x) {
    a_x := 1000;
  }



  while (*) {
    a_x := a_x + 1;
    if (x == y) {
      a_y := a_x + 1;
    }
    a_y := a_y - 1;
    if (y == x) {
      a_x := a_y + 1;
    }

  }

  if (a_x == 1000) {
    assert (a_y <= 0);
  }

} 
