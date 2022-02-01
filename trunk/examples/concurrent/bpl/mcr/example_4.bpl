//#Safe
/*
 * Date: 2020-01-16
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x0, x1, x2, x3: int;

procedure ULTIMATE.start()
modifies x0, x1, x2, x3;
{
    fork 0 set_0();
    fork 1 set_1();
    fork 2 set_2();
    fork 3 set_3();
    join 0;
    join 1;
    join 2;
    join 3;
    assert x0 == x1 && x1 == x2 && x2 == x3;
}

procedure set_0()
modifies x0;
{
    x0 := 0;
}

procedure set_1()
modifies x1;
{
    x1 := 0;
}

procedure set_2()
modifies x2;
{
    x2 := 0;
}

procedure set_3()
modifies x3;
{
    x3 := 0;
}
