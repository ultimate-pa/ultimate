//#Safe
procedure main() {
    var i, x, y : int;
    i := 0;
    
	assume (x + y) % 5 == 0;
	assume x % 5 == 1;

	while (i <= 10) {
		i := i + 1;
        x := x + 1;
	}

	assert y % 5 == 4;
}
