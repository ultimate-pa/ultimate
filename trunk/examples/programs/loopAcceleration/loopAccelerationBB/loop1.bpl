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
  y := 0;
  while (x <= 20){
    x := x + 2;
    y := y + 1;
  }
  assume y * 2 == x;
}
