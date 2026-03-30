//#Safe

var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    assume x == 0;
    assume y == 0;
    fork 1 Thread1();
    assert y < 3;
}

procedure Thread1()
modifies x, y;
{  
    while (1 == 1) {
        if (y < 1) {
            y := y + 1;
        }
        x := x + 1;
    }
}
