//#Safe
procedure ULTIMATE.start() {
	var x, y: int;
	x := 1;
	y := 2;
	x := -y + 8;
	assert x == -y + 8;
}
