//#Unsafe

procedure ULTIMATE.start()
{
	var x, y : int;
	var b : bool;

	x := 0;
	assert true;

	assume y >= 0 && y <= 10;
	assert true;

	b := false;
	assert true;

	assume b ==> y == 20;
	assert false;
}
