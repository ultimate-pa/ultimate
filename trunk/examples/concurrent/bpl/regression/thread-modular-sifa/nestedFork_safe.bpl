/*
    Simple case for handling nested forks, y is 2 or 3
*/

var y: int;

procedure ULTIMATE.start() returns()
modifies y;
{
    y := 0;
    fork 1 first();
    if (y == 1) {
        y := 2;
    }
}

procedure first() returns()
modifies y;
{
    y := 1;
    fork 3 second();
}

procedure second() returns()
modifies y;
{
    if (y == 1) {
        y := 3;
    }
    assert y == 3 || y == 2;
}
