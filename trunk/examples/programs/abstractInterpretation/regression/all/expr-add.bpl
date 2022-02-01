//#Unsafe
// inverse
procedure foo() {
	var x: int;
	assume x>=0 && x<=10;
	assert true;
	assume x + 5 == 7;
	assert x == 7;
}