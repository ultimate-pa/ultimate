//#Unsafe
// This program is a simpler version of stmt-bool-assume-9.bpl.
// The goal is that the disjunction leads to either two states, or a merge of
// both states, thus resulting in b to be TOP.

procedure ULTIMATE.start()
{
	var a, b : bool;

	assume ((a && b) || (!a && !b));

	// b should be TOP here. Thus, the assertion should fail.
	assert !b;
}
