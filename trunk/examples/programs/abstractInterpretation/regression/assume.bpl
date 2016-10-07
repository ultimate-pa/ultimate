//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= 0 && x <= 10;
	assume y >= 0 && y <= 10;

	assert true;
	assume x - y == -10;

	assert true;
	assert x == 0 && y == 10;
}
