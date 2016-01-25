//#Unsafe
// condition evaluation in condition always leaves an executable path
procedure foo() {
	var x,a: int;
	assume (if x == 0 && x == 1 then a == 1 else a == 0);
	assert a == 0;
}