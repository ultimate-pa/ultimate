//#Safe
procedure ULTIMATE.start() {
	var x, y : int;
	assume x <= y;
	assert x <= y;
	assert y >= x;
	assert x - y <= 0;
	assert y - x >= 0;
}
