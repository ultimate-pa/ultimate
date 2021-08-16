//#Safe
/*
 * Author: Miriam Herzig
 * Date: 2021-03-27
 * 
 */

procedure main() returns () {
  var x, y : int;
  while(y > 0 && x < 0)
  {
	y := y - 1;
	havoc x;
  }
}
