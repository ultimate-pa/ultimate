//#Safe
/*
 * Author: Miriam Herzig
 * Date: 2021-01-28
 * 
 */

procedure main() returns () {
  var x1, x2, x3, x4 : int;
  while(x1 > 0 && x2 > 0)
  {
      x1 := x1 + x2;
	  x2 := x2 + 1;
	  x3 := 1;
	  x4 := -x4 + 1;
  }
}
