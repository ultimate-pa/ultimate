//#Unsafe
// division should produce the intervall [ -2; 2 ]
procedure foo() {
	var a, y: int;

	assume y >= -16 && y <= 16;
	assert true;
	
	a := y / 8;
	assert a < 0;
}
