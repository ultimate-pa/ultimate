//#Unsafe
var x: int;
var y: int;

procedure ULTIMATE.start()
modifies x;
modifies y;
{
    x := 0;
    y := 0;
    fork 1 havocX();
    assert x == 0;
}

procedure havocX()
modifies x;
{
    havoc x;
}
