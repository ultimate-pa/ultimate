//#Safe
/*
 * Date: 2019-11-13
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y, z: int;

procedure ULTIMATE.start()
modifies x, y, z;
{
    fork 1 set_x();
    fork 2 set_y();
    fork 3 set_z();
    join 1;
    join 2;
    join 3;
    assert x == y && y == z;
}

procedure set_x()
modifies x;
{
    x := 0;
}

procedure set_y()
modifies y;
{
    y := 0;
}

procedure set_z()
modifies z;
{
    z := 0;
}
