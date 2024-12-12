//#Safe
/*
 * Revealed a but in our quantifier elimination.
 * 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-14
 */


var a : [int]int;
var i : int;

procedure main() returns (#res : int)
modifies a, i;
{
    i := 0;
    while (i < 1000000)
    {
        if (!(i < 1000000)) {
            break;
        }
        a[i] := 42;
        i := 1 + i;
    }
    i := 1048;
    assert 42 == a[i];
    return;
}

