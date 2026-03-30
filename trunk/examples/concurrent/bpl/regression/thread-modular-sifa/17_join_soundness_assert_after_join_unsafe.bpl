//#Unsafe
// Post-join assignment must execute even when joined thread writes the same variable.

var g: int;

procedure ULTIMATE.start()
modifies g;
{
    g := 0;
    fork 1 worker();
    join 1;
    g := 42;
    assert g != 42;
}

procedure worker()
modifies g;
{
    g := 1;
}
