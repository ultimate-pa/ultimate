//#Unsafe

procedure ULTIMATE.start()
{
	var x, y : int;
	var b : bool;

	x := 0;
	assert true;

	assume y >= 0 && y <= 10;
	assert true;

	assume b == ((x == 0) <==> (y == 5));
	assert false;
}
