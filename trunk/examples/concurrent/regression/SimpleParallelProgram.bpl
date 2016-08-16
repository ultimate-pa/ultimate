//#cSafe
/*
 * Author: raetherc@informatik.uni-freiburg.de
 * Date: 04.08.2016
 *
 * simple example for a parallel program with two threads
 */

var x: int;

procedure ~init() returns();
modifies x;

implementation ~init()
{
    // Pre condition
    x := 0;
}

procedure Thread0() returns ();
modifies x;

implementation Thread0()
{
    x := x + 1;
    //assert (x > 0);
    assert (x <= 3);
}

procedure Thread1() returns ();
modifies x;

implementation Thread1()
{
    x := x + 2;
}
