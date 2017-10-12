//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= 0 && x <= 10 && y >= 2 && y <= 20;

	assert true;
	x := x + 1;
	y := y + 5;

	assert x >= 1 && x <= 11 && y >= 7 && y <= 25;
	assert true;

	assume x == 10 && y == 15;

	assert x + y == 25 && x == 10;
}
