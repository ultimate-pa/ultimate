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
    join 1;
    
}

procedure foo();

implementation foo()
{
    assert f == true;
}