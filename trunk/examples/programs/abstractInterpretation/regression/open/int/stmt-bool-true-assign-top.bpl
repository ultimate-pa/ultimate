//#Safe

procedure ULTIMATE.start() {
	var a, b : bool;
	a := true;

	assert true;
	a := b;

	assert true;
	assume a != true;
	assert a == false;
}

