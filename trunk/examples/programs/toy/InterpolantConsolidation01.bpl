//#Safe
// Author: Betim Musa (musab@informatik.uni-freiburg.de)
// 25.06.15
var a, b : int;

procedure main() 
modifies a, b;
{
	a := 0;
	b := -1; 
	while (b < a) {
		b := b + 1;
	}
	assert (a == b);
}


