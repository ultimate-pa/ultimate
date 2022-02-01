procedure main() returns ()
{
  var x : int;
  call x := addOne(7);
  assert x == 8;
}

procedure addOne(in : int) returns (out : int)
{
	out := in + 1;
}

