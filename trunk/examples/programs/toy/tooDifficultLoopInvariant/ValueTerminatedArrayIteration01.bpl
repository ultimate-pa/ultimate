//#Safe
/* Motivated by difficult TermComp memorysafety problems.
 * We can solve it with FPBP and Predicate Cannibalization.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-08-18
 */
var i,end : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	assume end >= 0;
	a[end] := 42;
	i := 0;
	while (a[i] != 42) {
		i := i + 1;
	}
	assert i <= end;
}

