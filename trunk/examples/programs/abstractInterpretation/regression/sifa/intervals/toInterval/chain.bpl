//#Safe
procedure main() {
	var a, b, c, d, e : int;
	assume a == b && b == c && c == d && d == e && e == 7;
	assert true;
}
