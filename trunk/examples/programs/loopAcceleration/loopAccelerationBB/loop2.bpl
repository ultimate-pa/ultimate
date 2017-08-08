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
  x := 15;
  y := 0;
  while (x > 10){
    x := x - 1;
    y := y + 2;
  }
  x := x + 7;
}
