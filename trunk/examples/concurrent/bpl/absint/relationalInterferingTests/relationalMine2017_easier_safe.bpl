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
    while (true) {
        if (x < y) {
            x := x + 1;
	    assert x > 0;
            assert x <= y;
            assert x <= 4;
        }
    }
}

procedure Thread2()
modifies x, y;
{  
    while (true) {
        if (y < 4) {
            y := y + 1;
            assert x <= y;
        }
    }
}
