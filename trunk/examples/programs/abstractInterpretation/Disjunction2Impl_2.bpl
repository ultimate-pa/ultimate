//#Safe
/*
 * Test if the analysis can handle 
 * disjunctive formulas
 */

procedure Disjunct2_impl2() 
{
	var x, y, z: int;
	
	havoc x;
	havoc y;
	
	z := 0;
	
	// only x or y gets necessarily set to > 0
	if(x < 0)
	{
		x := -x;
	}
	else if(y < 0)
	{
		y := -y;
	}


	if(x > 1)
	{
		z := z + 1;
	}
	if(y > 1)
	{
		z := z + 1;
	}

	assert ((x < 0 || y < 0) ==> (z <= 1));
}