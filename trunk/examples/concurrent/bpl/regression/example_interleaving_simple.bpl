//#Safe
/*
 * Date: 2019-11-26
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    fork 1 set_x();
    y := 0;
    join 1;
    assert x == y;
}

procedure set_x()
modifies x;
{
    x := 0;
}