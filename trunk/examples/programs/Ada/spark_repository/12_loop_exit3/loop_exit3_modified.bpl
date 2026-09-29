procedure Loop_Exit3()
{
  var X: int;
  var Y: bool;
  var I: int;

  X := 1;
  Y := false;

  while (X > 0)
  {
    Y := false;
    while (X > 0)
    {
      if (X > 0) {
        X := 0;
        Y := true;
        break;
      }
      I := 1;
      while (I <= 3)
      {
        I := I + 1;
      }
    }
    assert Y == true;
  }
}
