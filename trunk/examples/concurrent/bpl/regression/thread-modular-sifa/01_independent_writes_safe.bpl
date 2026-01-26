var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    x := 0;
    y := 0;
    fork 1 writer_x();
    y := 1;
    
    assert x == 0 || x == 1;
    assert y == 1;
}

procedure writer_x()
modifies x;
{
    x := 1;
}
