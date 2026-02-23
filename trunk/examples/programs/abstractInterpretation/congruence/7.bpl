procedure main() {
    var i, x : int;
    i := 0;
    x := 0;

	while (i <= 10) {
		i := i + 1;

		if (i % 3 == 0) {
			x := x + 1;
		}
        
	}

	assert x == 3;
}
