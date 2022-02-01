//#Safe

procedure ULTIMATE.start() {
	var x, y : int;

	havoc x, y;
	assume x >= 5;
	call y := abs(x);
	assert y >= 5;

	// new inputs are a subset of the old inputs => old summary will be re-used
	// old summary is not sufficient to prove correctness in this case
	havoc x, y;
	assume x >= 6;
	call y := abs(x);
	assert y >= 6;
}

procedure abs(i : int) returns (o : int) {
	if (i < 0) {
		o := -i;
	} else {
		o := i;
	}
}

