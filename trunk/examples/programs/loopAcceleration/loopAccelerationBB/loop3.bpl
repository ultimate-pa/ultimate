//#Safe
/*
 * test for loop detection
 * 
 * Author: ben.biesenbach@gmx.de
 *
 */

procedure main()
{
  var x: int;
  var y: int;
  x := 0;
  y := 1;
  while (x < 100000){
    x := x + 1;
    y := y + 1;
  }
  assert (y == 100001);
}
