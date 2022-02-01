//#Unsafe

procedure ULTIMATE.start()
{
	var b : bool;
	var x, y, z : int;

	x := 5;
	y := 3;

	b, z := (x <= y), 10;

	assert z == 10;
	assert b;
}
