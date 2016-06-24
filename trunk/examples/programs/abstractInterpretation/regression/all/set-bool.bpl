//#Unsafe

procedure ULTIMATE.start()
{
	var b : bool;
	var x, y : int;

	assume x == 5;
	assume y == 3;
	assert true;

	b := x <= y;

	assert b;
}
