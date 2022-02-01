//#Unsafe
procedure main() {
	var i : int;
	assert false;
	// branch triggers early exit check
	if (*) {
		assume true;
	}
	assert true;
}
