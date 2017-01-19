//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;
	
	x := 0;
	y := 1;

	assert true;
	x := x + 5;
	y := x - y;

	assert true;
	assert x == 5 && y == 4;
}
