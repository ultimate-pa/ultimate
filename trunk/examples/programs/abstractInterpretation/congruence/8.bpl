procedure main() {
    var i, x, y, m : int;
	var b : bool;

    i := 1;
	x := 2;
	y := 0;

	while (i < m) {
		havoc b;

		if (b) {
			x := x + 4;
		} else {
			x := x + 2;
			y := y + 1;
		}
        
		i := i + 1;
	}

	assert x % 2 == 0;
	assert (x + 2 * y) % 4 == 2;
}
