//#Safe
/*
 * Example that is only verified succesfully if use use
 * ForwardPredicates, BackwardPredicates and Interpolant Cannibalization
 * Author: heizmann@informatik.uni-freiburg.de, Betim Musa
 * Date: 2014-10-15
 */
var x, y : int;

procedure main() 
modifies x, y;
{
	assume (x % 2 == 0 && y == 42);
	while (*) {
		x := x + 2;
		y := y + 2;
	}
	assert (y % 2 == 0 && x != 23);
}



