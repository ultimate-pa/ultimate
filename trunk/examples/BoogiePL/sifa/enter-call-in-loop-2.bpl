procedure main() returns ()
{
	var x : int;
	call sub();
	while (*) {
		x := 1;
		call sub();
		x := 2;
	}
	assert true;
}

procedure sub() returns ()
{
	var y : int;
	y := 1;
	assert true;
	y := 2;
}

