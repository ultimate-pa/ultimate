//#Terminating
// Switch of termination argument simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-05-23

var x : int;
var a, b, c : [int]int;

procedure proc() returns ()
modifies a, b, c;
{
    assume b == c;
    a[23] := b[23];
    while (a[x] > 0) {
        a[x] := a[x] - 1;
    }
}


