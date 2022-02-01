//#Unsafe

procedure ULTIMATE.start()
{
	var b : bool;
	var x, y : int;

	assume x >= -10 && x <= 0;
	assume y >= 0 && y <= 10;

	assert true;
	assume b == (x >= y);

	assert true;
	assert !b;
}
