//#Safe
/*
 * test for loop detection
 * 
 * Author: ben.biesenbach@gmx.de
 *
 */
var x,y : int;
procedure main() returns () modifies x,y;{
	x := 10;
	while (x < 100) {
		x := x + 2;
	}
	assert (x == 100 || x == 101);
}
