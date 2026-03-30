//#Safe
/*
    Without location abstraction, this would create x->inf,
    for any other standard thread-mod absint. 
*/

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    x := x + 1;
    assert x >= 2;
    assert x <= 3;
}

procedure one()
modifies x;
{
    x := x + 1;
}
