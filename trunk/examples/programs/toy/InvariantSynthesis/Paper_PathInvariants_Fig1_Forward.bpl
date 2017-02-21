//#Safe
/* Date: 2016-02-04
 * Author: musab@informatik.uni-freiburg.de
 * Example in Figure 1 from Paper "Path Invariants" published in 2007 (D.Beyer, T.A.Henzinger, R.Majumdar).
 * 
 */

var a, b, i, n : int;

procedure forward() returns ()
modifies a, b, i;
{
	assume (n >= 0);
	i := 0;
	a := 0;
	b := 0;
	while (i < n) {
		if (*) {
			a := a + 1;
			b := b + 2;
		} else {
			a := a + 2;
			b := b + 1;
		}
		i := i + 1;
	}
	assert (a + b == 3 * n);
}


