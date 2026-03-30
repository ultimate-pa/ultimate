var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    x := 0;
    y := 0;
    fork 1 Thread1();
    fork 2 Thread2();
    assert x <= y;
}

procedure Thread1()
modifies x, y;
{  
    while (1 == 1) {
        if (x < y) {
            x := x + 1;
        }
    }
}

procedure Thread2()
modifies x, y;
{  
    while (1 == 1) {
        if (y < 10) {
            y := y + 1;
            x := (x + y) / 2;
        }
    }
}
