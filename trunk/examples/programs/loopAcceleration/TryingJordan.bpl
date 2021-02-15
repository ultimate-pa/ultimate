//#Safe
/*
 * Author: Miriam Herzig
 * Date: 2021-01-28
 * 
 */

procedure main() returns () {
  var x1, x2, x3 : int;
  while(x1 > 0 && x2 > 0)
  {
      x1 := -x1 + x3 + 3;
	  x2 := x1 + x2;
  }
}
