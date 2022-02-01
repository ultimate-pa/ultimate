//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple, incorrect toy program without loops.
 *
 */

procedure loopFreeEx()
{
  var x, y: int;

  x := 0;
  y := 0;

  if (*) {
   x := 5;
   y := 7;
  }
  else {
   y := 4;
   if (x>=0) {
     x := x + 1;
     assert(x==0);
   }
  }

  if (*) {
    x := x + 1;
  }

  assert(x != -1);
  x := y + 1;
  assert(y != -1);
  x := x + 1;
}

