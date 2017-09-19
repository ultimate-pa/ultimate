//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x == 0 && y == 1;

	assert x == 0 && y == 1;
}
