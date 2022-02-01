//#Safe

procedure ULTIMATE.start()
{
	var x : int;

	assume x >= 0 && x <= 10;

	assert true;
	x := x + 1;

	assert true;
	assert x >= 1 && x <= 11;
}
