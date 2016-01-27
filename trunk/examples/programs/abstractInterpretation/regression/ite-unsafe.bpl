//#Unsafe
// condition evaluation in condition always leaves an executable path
procedure foo() {
	var x,a: int;
	assume (if x == 0 && x == 1 then a == 0 else a == 1);
	assert a != 1;
}
