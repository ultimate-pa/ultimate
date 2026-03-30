//#Unsafe
// Post-join code must be reachable.

var g: int;

procedure ULTIMATE.start()
modifies g;
{
    g := 0;
    fork 1 worker();
    join 1;
    assert 0 == 1;
}

procedure worker()
modifies g;
{
    g := 1;
}
