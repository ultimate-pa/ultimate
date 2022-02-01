//#Safe

procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume x <= 0 && z == y && x == y;
	
	assert true;
	assert z <= 0;
}
