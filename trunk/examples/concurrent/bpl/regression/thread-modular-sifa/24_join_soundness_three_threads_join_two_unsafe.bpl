//#Unsafe
// A not-yet-joined third worker can still invalidate facts from already joined workers.

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 set_one();
    fork 2 set_two();
    fork 3 set_zero();
    join 1;
    join 2;
    assert x == 2;
}

procedure set_one()
modifies x;
{
    x := 1;
}

procedure set_two()
modifies x;
{
    x := 2;
}

procedure set_zero()
modifies x;
{
    x := 0;
}
