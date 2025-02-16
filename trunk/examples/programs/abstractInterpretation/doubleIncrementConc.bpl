//#Safe

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    x := x + 1;
}

procedure one()
modifies x;
{
    x := x + 1;
}
