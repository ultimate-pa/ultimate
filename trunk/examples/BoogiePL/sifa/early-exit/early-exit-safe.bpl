//#Safe
procedure main() {
	var i : int;
	assume false;
	// branch triggers early exit check
	if (*) {
		assume true;
	}
	assert true;
}
