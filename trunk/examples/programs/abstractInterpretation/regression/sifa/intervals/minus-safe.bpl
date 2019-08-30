//#Safe
procedure main() {
	var x, y : real;
	assume x >= 4.0 && x <= 9.3;
	assume y >= -2.8 && y <= 0.9;
	x := x - y;
	assert x >= 3.1 && x <= 12.1;
}
