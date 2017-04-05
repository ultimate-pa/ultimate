//#Unsafe
procedure foo() {
	var x: int;
	x := 0;
	
	while (x < 100000) {
		x := x + 1;
	}
	
	assert false;
}