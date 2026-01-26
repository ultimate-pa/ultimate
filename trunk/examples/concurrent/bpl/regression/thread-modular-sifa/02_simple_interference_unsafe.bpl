//#Unsafe

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 writer();
    assert x == 0;
}

procedure writer()
modifies x;
{
    x := 1;
}
