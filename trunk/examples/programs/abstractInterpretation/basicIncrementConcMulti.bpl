//#Safe

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    fork 2 two();
}

procedure one()
modifies x;
{
    x := x + 1;
    fork 3 two();
}

procedure two()
modifies x;
{
    x := x + 1;
}
