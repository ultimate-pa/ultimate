//#Unsafe
/*
 * Date: 07.02.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Similar than TestSequentialComposition, but here
 * - case 3 is not   y := a;   but   havoc y;
 * - all assert statements should fail,
 * - and the cases where 3 does not occur are omited.
 *
 * cases:
 * 1. y does not occur: assume(true)
 * 2. y is only inVar: a := y;
 * 3. y is only outVar: havoc y;
 * 4. y is inVar and outVar y := y + 1;
 */

procedure proc()
{
  var in, a, y: int;

  //case 1-3
  y,a := 0, 10;
  assume(true);
  havoc y;
  assert (y == 0);

  
  //case 2-3
  y,a := 0, 10;
  a := y;
  havoc y;
  assert (y == 0);

  
  // case 3-1
  y,a := 0, 10;
  havoc y;
  assume(true);
  assert(y == 0);

  
  //case 3-2
  y,a := 0, 10;
  havoc y;
  a := y;
  assert (y == 0);

  
  //case 3-3
  y,a := 0, 10;
  havoc y;
  havoc y;
  assert (y == 0);

  
  //case 3-4
  y,a := 0, 10;
  havoc y;
  y := y + 1;
  assert (y == 1);
      

  //case 4-3
  y,a := 0, 10;
  y := y + 1;
  havoc y;
  assert (y == 1);

}
