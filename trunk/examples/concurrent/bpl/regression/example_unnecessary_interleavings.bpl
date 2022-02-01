//#Safe
/*
 * Date: 2019-12-12
 * schuessf@informatik.uni-freiburg.de
 *
 */

var i, x, y, z: int;

procedure ULTIMATE.start()
modifies i, x, y, z;
{
    i := 0;
    fork 1 set_x();
    fork 2 set_y();
    fork 3 set_z();
    join 1;
    join 2;
    join 3;
    assert i == 0;
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
