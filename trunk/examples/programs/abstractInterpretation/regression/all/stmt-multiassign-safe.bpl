//#Safe
// 13.07.2016: Tests how multiassign statements are handled.

procedure ULTIMATE.start()
{
	var x, y : int;
	
	x := 0;
	
	x, y := x + 1, x + 1;
	assert true;
	
	assert x == 1 && y == 1;
}