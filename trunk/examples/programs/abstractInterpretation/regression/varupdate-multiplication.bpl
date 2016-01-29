//#Unsafe

procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume x >= 1 && x <= 10;
	assume y == -2 || y == 2;

	assert true;
	assume x / y == 5;

	assert true;
	assert false;
}
