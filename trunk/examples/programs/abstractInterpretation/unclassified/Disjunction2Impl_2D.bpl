//#Safe
/*
 * Test if the analysis can handle 
 * disjunctive formulas
 */

procedure Disjunct2Impl_2D() 
{
	var x, z: int;
	
	havoc x;
	
	z := 0;
	
	if(x > 1)
	{
		z := z + 1;
	}
	if(x < -1)
	{
		z := z + 1;
	}

	assert ((x < 0 || x > 0) ==> (z <= 1));
}