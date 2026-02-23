procedure main() {
	var i, x : int;
    i := 0;

    assume x % 2 == 0;

	while (i <= 10) {
		i := i + 1;
        x := x + 2;
	}

	assert x % 2 == 0;
}
