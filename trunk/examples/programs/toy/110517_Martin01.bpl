procedure foo() {
	var x: int;
	x := 0;
	
	while (x < 1000000) {
		x := x + 1;
	}
	
	assert false;
}