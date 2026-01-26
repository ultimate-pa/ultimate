//#Unsafe

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 1 worker1();
    fork 2 worker2();
    assert x == 0;
    join 1;
    join 2;
}

procedure worker1()
modifies x;
{
    x := 1;
}

procedure worker2()
modifies x;
{
    x := 2;
}
