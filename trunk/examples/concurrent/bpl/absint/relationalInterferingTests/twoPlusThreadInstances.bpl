//#Safe
/*
    Atm threads with more than 1 instance are treated as inf instances.
    This would lead to x-> inf accordingly.
    Precise handling of threadinstances should create precise annotation.
*/

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    fork 2 one();
    x := x + 1;
}

procedure one()
modifies x;
{
    x := x + 1;
}
