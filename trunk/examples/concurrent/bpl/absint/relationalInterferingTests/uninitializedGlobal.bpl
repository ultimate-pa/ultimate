//#Safe
/*
    Potentially uninitialized y leads to weird behaviour. 
*/

var x : int; 
var y : int; 
 
procedure ULTIMATE.start()
modifies x;
modifies y;
{
    x := 1;
    fork 1 one();
    x := x + 1;
    x := x + y;
}

procedure one()
modifies y;
{
    y := 1;
}
