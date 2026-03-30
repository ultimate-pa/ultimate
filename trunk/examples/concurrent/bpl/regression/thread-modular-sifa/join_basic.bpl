// #Safe

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    fork 2, 0, 0 one();
    x := 1;
    join 2, 0, 0;
    x := 1;
    x := 1;
    x := 1;
    x := 1;
}

procedure one()
modifies x;
{
    x :=  1;
    x :=  2;
}

