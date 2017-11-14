//#Safe

procedure ULTIMATE.start()
{
	var a, b, c, res : int;

	a := b;
	havoc b;

	c := a;
	if (a == 1) {
		res := 1;
	} else {
		a := 1;
		res := 2 * 1;
	}

	if (res != 0) {
	} else {
		assert false;
	}
}
