
procedure inc(x : int) returns (res: int)
{
	var y : int;

	if(x > 10){
		res := x + 1;
	} else{
		y := x + 5;
		call res := inc(y);
	}
}

procedure Main() returns ()
{
  var z : int;
  var y : int;
  y := 0;
  call z := inc(y);
  assert(z == 0);
}




