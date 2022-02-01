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
    x := x * y;
    y := y + 1;
  }
  assume y == x;
}
