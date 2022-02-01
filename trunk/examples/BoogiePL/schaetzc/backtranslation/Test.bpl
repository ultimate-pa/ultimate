
procedure inc(x : int) returns (res: int)
requires true;
ensures true;
{
  call doNothing();
  call doNothing();
}


procedure doNothing()
//requires true;
//ensures true; 
{
  assume true;
}


procedure Main() returns ()
{
  var z : int;
  z := 0;
  call z := inc(2);
  //call z := inc(2);
  assert false;
}

