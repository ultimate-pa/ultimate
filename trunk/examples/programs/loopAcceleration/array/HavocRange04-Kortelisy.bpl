//#Safe
/*
 * Very similar than HavocRange03-Ratne, but here the number of iterations is 
 * bounded by a literal which makes the resulting trace formula significantly
 * simpler for SMTInterpol and overall verification significantly faster.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-26
 */
var i,x : int;
var a : [int]int;
var N : int;

procedure main() 
modifies a, i, x;
{
	a[123456] := 42;
	i := 0;
	while (i < 1234567) {
		havoc x;
		assume x < 77;
		a[i] := x;
		havoc x;
		i := i + 1;
	}
	assert(a[123456] < 100);
}
