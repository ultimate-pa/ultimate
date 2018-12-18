//#Safe
/*
 * 
 * Date: 2017-03-08
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y, xold, yold : int;
  var a : [int]int;
  
  y := x + 1;
  a[x] := 1000;
  a[y] := 0;

  while (*) {
	  xold := x;
	  yold := y;
	  x := (x + 1) % 256;
	  y := (y + 1) % 256;
	  a[x] := a[xold];
	  a[y] := a[yold];
  }

  if (a[x] == 0) {
    assert (a[y] == 1000);
  }
} 
