//#Unsafe
// assume [0;8] % 4 == 0 results in [0;8] because concrete states are 0,4,8
procedure foo() {
	var x: int;
	assume x>=0 && x<=8;
	assert true;
	assume x % 4 == 0;
	assert x != 8;
}