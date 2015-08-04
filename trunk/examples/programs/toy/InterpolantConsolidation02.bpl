//#Safe
// Author: Betim Musa (musab@informatik.uni-freiburg.de)
// 3.07.15
var a, b, c, d : int;

procedure main() 
modifies a, b, c, d;
{
	a := 3;
	b := 5; 
	c := b;
	d := 10;
	while (a < d) {
		a := a + 1;
	}
	assert (c * a == b * d);
}


