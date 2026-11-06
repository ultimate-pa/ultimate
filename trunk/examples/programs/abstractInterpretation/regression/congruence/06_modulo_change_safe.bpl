//#Safe
procedure main() {
    var i, x, y : int;
    i := 0;
    
	assume (2 * x + 3 * y) % 5 == 0;
	assume x % 10 == 1;

	while (i <= 10) {
		i := i + 1;
        x := x + 1;
	}

	assert y % 5 == 1;
}
