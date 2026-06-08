//#Unsafe
// Joining one worker must not import global facts that another live worker can invalidate.

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 set_one();
    fork 2 set_zero();
    fork 3 idle();
    join 1;
    assert x == 1;
}

procedure set_one()
modifies x;
{
    x := 1;
}

procedure set_zero()
modifies x;
{
    x := 0;
}

procedure idle()
{
}
