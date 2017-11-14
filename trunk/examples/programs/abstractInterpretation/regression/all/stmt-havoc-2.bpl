//#Safe

procedure ULTIMATE.start()
{
	var a, b : int;

	assume a >= 0 && a <= 10;
	assert true;

	b := a;
	havoc a;

	assert b >= 0 && b <= 10;
}
