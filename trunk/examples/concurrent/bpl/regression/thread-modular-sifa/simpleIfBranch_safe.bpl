//#Safe
/*
    Branch-sensitivity
*/

var x : int; 
var y : int; 
 
procedure ULTIMATE.start()
modifies x;
modifies y;
{
    x := 16;
    y := 1;
    fork 1 one();
}

procedure one()
modifies y;
{
    if (x == 4) {
        y := 777;
    }
    if (x == 16) {
        y := 42;
    }
}
