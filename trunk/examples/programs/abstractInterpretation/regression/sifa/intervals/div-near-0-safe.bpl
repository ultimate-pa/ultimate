//#Safe
procedure main() {
	var x, y : real;
	assume x >= -5.0 && x <= 6.2;
	assume y >= 0.1 && y <= 3.0;
	x := x / y;
	assert x >= -50.0 && x <= 62.0;
}
