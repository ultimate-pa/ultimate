//#Unsafe
procedure EasyLoop() 
{
	var x, y: int;
	
	x := 0;
	y := 0;
	
	while(x < 35)
	{
		x := x + 1;
		y := y + 2;
		
		while(x < y)
		{
			x := x + 1;
		}
	}
	
	assert ( x < y );
}