//#Unsafe
var g : int;
implementation main() returns ()
{
    var x : int;
    var r : real;

    g := 0;
    x := 0;
    r := 0.0;
    havoc g, x, r;
    assert x == g;
}

procedure main() returns ();
    modifies g;
