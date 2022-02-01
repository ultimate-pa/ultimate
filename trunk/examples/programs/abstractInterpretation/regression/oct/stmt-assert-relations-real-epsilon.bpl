//#Safe
procedure ULTIMATE.start() {
	var x, y : real;
	assume x <= y;
	assert x <= y + 0.001;
	assert y >= x - 0.001;
	assert x - y <= 0.001;
	assert y - x >= -0.001;
}
