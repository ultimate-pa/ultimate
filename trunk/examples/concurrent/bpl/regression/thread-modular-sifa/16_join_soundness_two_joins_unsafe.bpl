//#Unsafe
// Two threads joined; both post-join states must be reachable.

var g: int;
var h: int;

procedure ULTIMATE.start()
modifies g, h;
{
    g := 0;
    h := 0;
    fork 1 worker_g();
    fork 2 worker_h();
    join 1;
    join 2;
    assert 0 == 1;
}

procedure worker_g()
modifies g;
{
    g := 1;
}

procedure worker_h()
modifies h;
{
    h := 1;
}
