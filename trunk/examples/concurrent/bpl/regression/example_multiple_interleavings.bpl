//#Safe
/*
 * Date: 2020-03-16
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    fork 1 set_x_0();
    fork 2 set_x_1();
    fork 3 set_y();
    join 1;
    join 2;
    join 3;
    assert y == 0 && (x == 0 || x == 1);
}

procedure set_x_0()
modifies x;
{
    x := 0;
}

procedure set_x_1()
modifies x;
{
    x := 1;
}

procedure set_y()
modifies y;
{
    y := 0;
}
