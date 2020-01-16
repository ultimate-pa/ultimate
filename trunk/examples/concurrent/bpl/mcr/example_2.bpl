//#Safe
/*
 * Date: 2020-01-16
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x0, x1: int;

procedure ULTIMATE.start()
modifies x0, x1;
{
    fork 0 set_0();
    fork 1 set_1();
    join 0;
    join 1;
    assert x0 == x1;
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
