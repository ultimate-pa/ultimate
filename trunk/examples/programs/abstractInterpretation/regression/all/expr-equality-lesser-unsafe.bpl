//#Unsafe
// lesser equal boundaries have to be considered 
procedure foo() {
	var x,y: int;
	x := 0;
	assume y >= 0 && y <=1;
	assert true;
	assume x < y;
	assert false;
}
