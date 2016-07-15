//#Unsafe
// [a,b] % n where n > a && n > b and a,b>=0 should be [a;b]
procedure foo() {
	var x: int;
	assume x>=0 && x<=10;
	assert true;
	assume x % 4294967296 <= 10;
	assert x!=10;
}