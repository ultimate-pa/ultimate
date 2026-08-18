procedure ULTIMATE.start()
{
  var x, z : int;

  fork 1 T1(1);
  fork 2 T2();
  fork 3 T1(3);

  if (*) {
    x := 1;
  } else {
    x := 2;
  }
  join x assign z;
  assert z != 3;
}

procedure T1(y : int) returns (z : int)
{
  z := y;
}

procedure T2() returns (val : int)
{
  val := 2;
}

procedure T3() returns (flag : bool, val : int)
{
  flag := true;
  val := 3;
}

