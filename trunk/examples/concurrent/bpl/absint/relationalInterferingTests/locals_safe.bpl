//#Safe
/*
    Interferences handle local variables correctly.
    As in, they aren't transferred in interferences.
*/

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    var y : int;
    x := 1;
    fork 1 one();
    y := 1;
    assert y == 1;
}

procedure one()
modifies x;
{
    var y : int;
    x := x + 1;
    y := 2;
    assert y == 2;
}
