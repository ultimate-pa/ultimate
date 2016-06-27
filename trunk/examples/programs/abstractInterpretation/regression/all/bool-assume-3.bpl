//#Unsafe

procedure ULTIMATE.start()
{
	var b : bool;

	assume b == false;
	assume !b;

	assert b;
}
