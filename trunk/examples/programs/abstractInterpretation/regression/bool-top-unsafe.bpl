//#Unsafe

procedure ULTIMATE.start()
{
	var b : bool;
	var x : int;

//	b := true;
	assert true;
	//assume b;
	assert true;
	x := 1;
	assert true;

	assume b == true;

	assert true;
//	assert b && x == 1;
	assert !b && x == 1;
}
