//#Unsafe
/*
 * Date: 2022-10-12
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x: int;

procedure ULTIMATE.start()
modifies x;
{
    fork 0 a();
}

procedure a()
modifies x;
{
    x := 0;
    x := 1;
    fork 1 b();
    assert x > 0;
}

procedure b()
modifies x;
{
    fork 3 a();
}
