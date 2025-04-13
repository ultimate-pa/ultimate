//#Unsafe
/*
    We handle infinite forked thread correctly.
*/

var x : int; 
var y : int; 
 
procedure ULTIMATE.start()
modifies x;
modifies y;
{
    x := 1;
    y := 1;
    while (*) {
        fork 1 one();
	assert x < 10;
    }
}

procedure one()
modifies x;
{
    x := x + y;
}
