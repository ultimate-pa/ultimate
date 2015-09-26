//#Safe
/*
 * Test if the analysis can handle 
 * disjunctive formulas
 */

procedure Disjunct() 
{
	var x, y, z: int;
	
	havoc x;
	havoc y;
	
	if(x < 0)
	{
		x := -x;
	}
	if(y < 0)
	{
		y := -y;
	}
		
	if(x < 10 || y < 10)
	{
		z := x + y - 10;
		
		if(x < y)
		{		
			assert (z <= y);
		}
		else
		{		
			assert (z <= x);
		}
	}	
}