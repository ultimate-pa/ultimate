//#Safe

procedure ULTIMATE.start()
{
	call lessThan();
	call greaterThan();
	call notEqual();
	call equal();
}

procedure lessThan()
{
	var x, y : int;
	
	assume -10*x <= 5; // <==> (-x <= 0.5) <==> (-x <= 1)
	assert -x <= 0;

	assume 2*y < -1; // <==> (y < -0.5) <==> (y <= -1)
	assert y <= -1;
}

procedure greaterThan()
{
	var x, y : int;
	
	assume 10*x >= 5; // <==> (x >= 0.5) <==> (x >= 1)
	assert x >= 1;

	assume -2*y > -1; // <==> (-y > -0.5) <==> (-y > 0)
	assert -y >= 0;
}

procedure notEqual()
{
	var x : int;
	assume 2*x != 1; // <==> (x != 0.5) <==> (true). 
	// TODO assert that x can have any value
}

procedure equal()
{
	var x : int;
	assume 2*x == 1; // <==> (x == 0.5) <==> (false).
	assert false;
}

