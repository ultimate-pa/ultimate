//#Safe
/*
 * A program that demonstrates when a semanticCheck is necessary in order to
 * be able to compose more statements.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-09-19
 * 
 */

var f : bool;


procedure ULTIMATE.start();
modifies f;

implementation ULTIMATE.start()
{
    fork 1 foo();
    f := true;
    assert f;
    join 1;
}

procedure foo();
modifies f;

implementation foo()
{
    f := true;
}