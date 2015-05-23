//#Terminating
// Bug with oldVars in supporting invariants. Switch of termination argument
// simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-05-20

var x, y, z : int;

procedure proc() returns ()
modifies x;
{
    while (x > 0) {
        x := x - y;
    }
}

procedure main() returns ()
modifies z, x;
{
    z := z - 1;
    call proc();
}


procedure ULTIMATE.start() returns ()
modifies x, y, z;
{
    y := 2;
    call main();
}


