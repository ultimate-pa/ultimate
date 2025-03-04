var x: int;
var y: int;

procedure ULTIMATE.start()
modifies x;
modifies y;
{
    x := 0;
    y := 0;
    fork 1 havocX();
    if (x == 1) {
        x := 2;
    }
}

procedure havocX()
modifies x;
{
    havoc x;
}
