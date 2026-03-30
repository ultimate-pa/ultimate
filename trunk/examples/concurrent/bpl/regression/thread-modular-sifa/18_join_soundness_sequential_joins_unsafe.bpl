//#Unsafe
// Sequential fork/join; both post-join states must be reachable.

var g: int;

procedure ULTIMATE.start()
modifies g;
{
    g := 0;
    fork 1 worker();
    join 1;
    g := g + 1;
    fork 2 worker();
    join 2;
    assert 0 == 1;
}

procedure worker()
modifies g;
{
    g := g + 10;
}
