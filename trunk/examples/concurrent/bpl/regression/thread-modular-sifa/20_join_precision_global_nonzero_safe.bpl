//#Safe
// After join, g must be nonzero.

var g: int;

procedure ULTIMATE.start()
modifies g;
{
    g := 0;
    fork 1 worker();
    join 1;
    assert g != 0;
}

procedure worker()
modifies g;
{
    g := 1;
}
