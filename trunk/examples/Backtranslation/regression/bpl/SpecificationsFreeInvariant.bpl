procedure foo() returns (res: int)
{
	var x,y : int;
	y := 1;
	x := 2;
	while(y>0)
	free invariant x > 0;
	{
		y := y - 1;
		x := x - 1;
	}
	assert false;
	
}



