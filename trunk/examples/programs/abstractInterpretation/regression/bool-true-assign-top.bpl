//#Safe

procedure ULTIMATE.start() {
	var a, b : bool;
	a := true;
	a := b;

	assume a != true;
	assert a == false;
}

