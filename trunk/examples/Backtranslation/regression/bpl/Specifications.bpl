
procedure inc(x : int) returns (res: int)
requires x > 0;
ensures res == x+x+x+x;
ensures res > x;
{
	var y : int;
	y := 4;
	while(y>0)
	invariant (y > 0);
	{
		res := res + x;
		y := y - 1;
	}
}

procedure Main() returns ()
{
  var z : int;
  z := 0;
  call z := inc(z);
}




