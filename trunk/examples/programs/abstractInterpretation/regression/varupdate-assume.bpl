//#Unsafe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= 0 && x <= 10;
	assume y >= 11 && y <= 20;
	
	assert true;
	assume x - x == 2;
	
	assert true;
	assert x != 8;
}
