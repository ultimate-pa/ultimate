//#Safe
procedure main() {
	var x, y : real;
	assume x >= -6.9 && x <= 5.4;
	assume y >= 2.3 && y <= 3.0;
	x := x / y;
	assert x >= -2.3  && x <= 1.8;
}
