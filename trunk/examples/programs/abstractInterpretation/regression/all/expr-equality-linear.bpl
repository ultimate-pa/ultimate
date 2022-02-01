//#Unsafe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= -10 && x <= 10;
	assume y >= -10 && y <= 10;

	assert true;
	assume x + y == 5;

	assert true;
	assert y != 5;
}
