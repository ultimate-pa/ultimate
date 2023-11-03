//#Safe
/*
 * A program that demonstrates how important Large Block Encoding can be.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-08-31
 * 
 */

var f : bool;

procedure ULTIMATE.start();
modifies f;

implementation ULTIMATE.start()
{
    f := true;
    fork 1 foo();
    fork 2 foo();
    fork 3 foo();
    fork 4 foo();
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    assert f == true;
    join 4;
    join 3;
    join 2;
    join 1;
}

procedure foo();

implementation foo()
{
    assert f == true;
    assert f == true;
}