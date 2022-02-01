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
	assume 3*x + -3*y <= 9;
	assert 2*x + -2*y <= 6;
	assert x - y <= 3;
}

procedure greaterThan()
{
	var x, y : int;
	assume -3*x + 3*y >= -12;
	assert -2*x + 2*y >= -8;
	assert -x + y >= -4;
}

procedure notEqual()
{
	var x, y : int;
	assume -2*x + -2*y != -4;
	assert -3*x + -3*y != -6;
	assert -x + -y != -2;
}

procedure equal()
{
	var x, y : int;
	assume  5*x +  5*y ==  5;
	assert -7*x + -7*y == -7;
	assert x + y == 1;
}

