//#Safe
// Two threads set flags; after joining both, both must be 1.

var flag1: int;
var flag2: int;

procedure ULTIMATE.start()
modifies flag1, flag2;
{
    flag1 := 0;
    flag2 := 0;
    fork 1 set_flag1();
    fork 2 set_flag2();
    join 1;
    assert flag1 == 1;
    join 2;
    assert flag2 == 1;
}

procedure set_flag1()
modifies flag1;
{
    flag1 := 1;
}

procedure set_flag2()
modifies flag2;
{
    flag2 := 1;
}
