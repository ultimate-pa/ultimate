//#Safe
procedure ULTIMATE.start() {
	var x, y: int;
	x := 3;
	y := -x;
	assert x == -y;
}
