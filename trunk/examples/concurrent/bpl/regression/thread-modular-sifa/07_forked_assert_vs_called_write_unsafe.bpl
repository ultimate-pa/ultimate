//#Unsafe

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 write_zero();
    call set_and_assert_one();
    join 1;
}

procedure set_and_assert_one()
modifies x;
{
    x := 1;
    assert x == 1;
}

procedure write_zero()
modifies x;
{
    x := 0;
}
