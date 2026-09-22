procedure ULTIMATE.start()
{
    var x : int;

    x := 0;

    fork 1 thread(x);
  
    join 1 assign x;

    assert x == 1;
}

procedure thread(x : int) returns (y : int)
{
  y := x + 1;
}
