procedure main() returns ()
{
  var i : int;
  i := 1;
  call sub();
  while(i < 2) {
  	i := i + 3;
  }
}

procedure sub() returns ()
{
  var j : int;
  j := 4;
  assert 5 > 0;
  j := 6;
  assert 7 > 0;
}

