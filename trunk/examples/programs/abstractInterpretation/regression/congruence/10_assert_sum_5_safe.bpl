//#Safe
procedure main() {
    var i, x, y, m : int;

    i := 1;
	x := 0;
	y := 0;

	while (i < m) {
		x := x + 2;
		y := y + 3;
        
		i := i + 1;
	}

	assert ( x + y ) % 5 == 0;
}
