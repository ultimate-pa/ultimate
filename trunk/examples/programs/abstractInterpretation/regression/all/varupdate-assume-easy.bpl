//#Unsafe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= 0 && x <= 10;
	assume y == 3;

	assert true;
	assume -x == -y;

	assert true;
	assert x != 3;
}
