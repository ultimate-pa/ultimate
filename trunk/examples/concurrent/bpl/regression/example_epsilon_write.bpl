//#Safe
/*
 * Date: 2019-12-16
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    fork 1 set_x();
    assume x > 0;
    join 1;
    assert x == 0;
}

procedure set_x()
modifies x;
{
    x := 0;
}