//#Unsafe
// A global join target must not be constrained by its value before the join.

var result: int;

procedure ULTIMATE.start()
modifies result;
{
    result := 0;
    fork 1 worker();
    join 1 assign result;
    assert result == 0;
}

procedure worker() returns (value: int)
{
    value := 1;
}
