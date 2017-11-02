//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x <= 6;

	assert true;
	assume x <= 0 && y == x;

	assert true;
	assert y <= 0;
}
