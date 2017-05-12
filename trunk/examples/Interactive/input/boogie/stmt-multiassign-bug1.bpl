//#Unsafe

procedure ULTIMATE.start()
{
  	var b : bool;
	var x, y, z : int;

	assume x >= 0 && x <= 10;
	y := 3;
	assert true;
	b, z := (x <= y), 5;

	assert z == 5;
	assert x < 3;   
}                       
