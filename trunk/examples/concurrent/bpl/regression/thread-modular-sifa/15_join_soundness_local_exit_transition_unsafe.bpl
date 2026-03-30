//#Unsafe
// Local-only exit transition must still update the location variable.

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
    var local: int;
    g := 1;
    local := 42;
}
