var x : int;

procedure ULTIMATE.start() // ~ghost~0 == 6 && 2 == x || ~ghost~0 == 2 || ~ghost~0 == 6 && 2 == x
modifies x;
{
    x := 0;

    fork 0 T1(); // ~ghost~0 == 1 || 5 == ~ghost~0 || ~ghost~0 == 4
    join 0; // x == 1 && ~ghost~0 == 3

    x := x + 1;

    assert x == 2; // false || ~ghost~0 == 6 && 2 == x
}

procedure T1() // ~ghost~0 == 4 || 5 == ~ghost~0 || 5 == ~ghost~0
modifies x;
{
    x := x + 1;
}

