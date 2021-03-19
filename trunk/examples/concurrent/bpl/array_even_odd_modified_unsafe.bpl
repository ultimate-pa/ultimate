//#Unsafe
// Author: Dennis Wölfing

var a : [int]int;
var i : int;
var j : int;

procedure ULTIMATE.start()
modifies a, i, j;
{
    i := 0;
    j := 1;
    fork 1 foo();
    fork 2 bar();
}

procedure foo()
modifies a, i;
{
    while (true) {
        a[i] := 0;
        assert a[i] == 0;
        i := i + 2;
        if (i == 6) {
            i := i + 1;
        }
    }
}

procedure bar()
modifies a, j;
{
    while (true) {
        a[j] := 1;
        assert a[j] == 1;
        j := j + 2;
    }
}
