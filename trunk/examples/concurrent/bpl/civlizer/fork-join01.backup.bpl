var x : int;

procedure ULTIMATE.start()
modifies x;
{
  // {true}

  assume x == 0;

  // {x == 0}

  fork 1 thread();
  
  //
  
  join 1;

  // {x == 1}

  assert x == 1;
}

procedure thread()
modifies x;
{
  // {x == 0}

  x := x + 1;

  // {x == 1}
}
