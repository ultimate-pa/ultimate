//#Safe

procedure ULTIMATE.start()
{
	var a, b : bool;

	b := true;

	assert true;
	assume a != b;
	assert b && !a;
}
