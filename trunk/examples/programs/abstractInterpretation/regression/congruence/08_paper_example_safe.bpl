//#Safe
procedure main() {
    var x, y, m, i : int;

    i := 1;
	x := 2;
	y := 0;

	while (i <= m) {
		if (*) {
			x := x + 4;
		} else {
			x := x + 2;
			y := y + 1;
		}
	}

	assert x % 2 == 0;
	assert (x + 2 * y) % 4 == 2;
}
