//#Safe

procedure ULTIMATE.start() {
	var x, y : int;
	assume x >= 5;
	call y := abs(x);
	assert y >= 5;
}

procedure abs(i : int) returns (o : int) {
	if (i < 0) {
		o := -i;
	} else {
		o := i;
	}
}

