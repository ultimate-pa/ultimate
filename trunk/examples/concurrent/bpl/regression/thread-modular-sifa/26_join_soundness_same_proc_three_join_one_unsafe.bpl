//#Unsafe
// Multiple instances of the same procedure: joining one instance is not enough to import stable globals.

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 increment_three_times();
    fork 2 increment_three_times();
    fork 3 increment_three_times();
    join 1;
    assert x >= 3;
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
