procedure My_Loop()
{
  var Loop_Cond: bool;

  Loop_Cond := true;

  while (Loop_Cond)
    invariant true;
  {
    Loop_Cond := false;
    assert Loop_Cond;
  }
}
