//#Unsafe
// The last live same-procedure instance can still perform stale writes after two joins.

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 increment_three_times();
    fork 2 increment_three_times();
    fork 3 increment_three_times();
    join 1;
    join 2;
    assert x >= 4;
}

procedure increment_three_times()
modifies x;
{
    var localx: int;

    localx := x;
    x := localx + 1;

    localx := x;
    x := localx + 1;

    localx := x;
    x := localx + 1;
}
