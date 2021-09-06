//#Safe
/*
 * Author: Miriam Herzig
 * Date: 2021-01-28
 * 
 */

procedure main() returns () {
  var x, y, z : int;
  while(x < 10)
  {
	x := x + 1;
	havoc y;
	z := z - 4;
  }
}
