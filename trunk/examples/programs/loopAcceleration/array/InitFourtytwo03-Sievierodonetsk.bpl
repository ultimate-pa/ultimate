//#Unsafe
/*
 * Test: Values outside range are not initialized.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-06-08
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[i] := 42;
		i := i + 1;
	}
	assert(a[-1] == 42 || a[1000000] == 42);
}
