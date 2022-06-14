//#Safe
/*
 * Test: Values outside range are unchanged.
 *
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-05-29
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
  	a[-1] := 23;
	a[1000000] := 23;
	i := 0;
	while (i < 1000000) {
		a[i] := 42;
		i := i + 1;
	}
	assert(a[-1] == 23 && a[1000000] == 23);
}
