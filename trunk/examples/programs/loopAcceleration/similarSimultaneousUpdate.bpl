//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-07
 * 
 * Example that demonstrates that the implementation
 * of the simultaneous update is insufficient.
 */

procedure main() returns () {
  var u, w, x, y, z : int;
  while(u > 0)
  {
      u := u - 1;
	  havoc w;
	  havoc x;
	  havoc y;
	  havoc z;
      assume u == z && z == w && w == x && x == y && y == z;
  }
}
