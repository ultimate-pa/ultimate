//#Terminating
// Bug with oldVars in supporting invariants. Switch of termination argument
// simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-05-23

var x, y, z : int;
var a, b, c : [int]int;

procedure proc() returns ()
modifies x, a, b, c, z;
{
    while (a[x] > 0) {
        a[x] := a[x] - b[y];
		
    }
}

procedure main() returns ()
modifies z, x, a, b, c;
{
    c[z] := c[z] - 1;
	a[z] := c[z];
    call proc();
}


procedure ULTIMATE.start() returns ()
modifies x, y, z, a, b, c;
{
    b[y] := 2;
    call main();
}


