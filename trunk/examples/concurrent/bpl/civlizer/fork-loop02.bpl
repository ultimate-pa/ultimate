var z : int;

procedure ULTIMATE.start()
modifies z;
{
  var x : int;

  z := 0;
  x := 2;
  while (x >= 0)
  {
    fork x T1();
    x := x - 1;
  }
  
  assert z <= 3;
}

procedure T1()
modifies z;
{
  z := z + 1;
}

