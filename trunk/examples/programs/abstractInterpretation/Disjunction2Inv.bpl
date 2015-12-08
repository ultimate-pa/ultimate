//#Safe
/*
 * Test if the analysis can handle 
 * disjunctive formulas
 */

procedure Disjunct3() 
{
	var x, y, z: int;
	
	havoc x;
	havoc y;
	
	z := 0;
	
	if(x > 1)
	{
		z := z + 1;
	}
	if(y > 1)
	{
		z := z + 1;
	}

	if(x < 0 || y < 0)
	{
		assert (z <= 1);
	}
}