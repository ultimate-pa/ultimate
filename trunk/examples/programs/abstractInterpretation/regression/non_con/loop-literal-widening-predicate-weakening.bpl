//#Safe
procedure ULTIMATE.start()
{
	var x, y, z, a, b, c : int;
	x := 1;
	y := 2;
	z := 3;
	a := 4;
	b := 5;
	c := 6;
	while (x < 100) {
		x := x + 1;
	}
	assert x <= 100;
}
