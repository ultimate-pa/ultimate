//#Safe

procedure ULTIMATE.start()
{
	var a, b : bool;

	assume ((a && b) || (!a && !b)) && !a;

	assert a == false;
}
