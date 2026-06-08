//#Unsafe
// After all joins, the post-join state must still be reachable.

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 set_one();
    fork 2 set_two();
    fork 3 set_three();
    join 1;
    join 2;
    join 3;
    assert 0 == 1;
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

procedure set_three()
modifies x;
{
    x := 3;
}
