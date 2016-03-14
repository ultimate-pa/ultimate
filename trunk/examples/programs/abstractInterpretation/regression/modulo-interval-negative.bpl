//#Unsafe

procedure ULTIMATE.start()
{
	var ab : int;
	assume -99 <= ab && ab <= 23;
	ab := ab % 25;
	assert ab == 24;
}
