//#Safe
/*
    State-sensitivity/what mine(2017) calls relational interferences
    needed to correctly handle this.
*/

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    if (x == 5) {
        x := 666;
    }
    if (x == 2) {
        x := 3;
    }
    assert x != 666;
}

procedure one()
modifies x;
{
    if (x == 1) {
        x := 2;
    }
    if (x == 3) {
        x := 5;
    }
    assert x == 2 || x == 3 || x == 5;
}
