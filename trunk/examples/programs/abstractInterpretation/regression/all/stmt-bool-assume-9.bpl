//#Safe

procedure ULTIMATE.start()
{
	var a, b : bool;

	assume ((a && b) || (!a && !b)) && !a;

	// a should be false here. Thus, the assertion should fail.
	assert !a;
}
