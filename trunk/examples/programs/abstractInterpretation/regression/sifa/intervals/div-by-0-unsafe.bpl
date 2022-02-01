//#Unsafe
procedure main() {
	var x, y : real;
	assume x == 1.0;
	assume y >= -1.0 && y <= 1.0;
	x := x / y;
	assert x >= -1.0 && x <= 1.0;
}
