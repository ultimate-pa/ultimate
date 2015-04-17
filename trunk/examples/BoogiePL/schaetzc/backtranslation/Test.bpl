
procedure inc(x : int) returns (res: int)
requires true;
ensures true;
{
  call doNothing();
}


procedure doNothing()
ensures true; 
{
}


procedure Main() returns ()
{
  var z : int;
  call z := inc(2);
  z := 0;
  assert false;
}

