//#Safe

procedure ULTIMATE.start()
{
	var x, y : int;

	assume x >= 0 && x <= 10;
	assume y >= 11 && y <= 20;
	
	assert true;
	assume y - x == 2;
	// possible abstract states: (x=9, y=11) or (x=10, y=12)
	
	assert true;
	assert x != 8;
}
