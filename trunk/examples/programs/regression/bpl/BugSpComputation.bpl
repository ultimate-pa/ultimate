//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 21.09.2013
 */

implementation main() returns (#res:int)
{
    var x, y, z : int;
    x := 0;
    y := x + 1;
    x := y;
    assert x == 1;
}


procedure main() returns (#res:int);
