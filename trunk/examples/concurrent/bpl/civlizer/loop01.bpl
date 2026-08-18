
var x : int;

procedure inc() returns()
modifies x;
{
    while (x < 100) {
	    x := x + 1;
    }
}

procedure dec() returns()
modifies x;
{
	x := x - 1;
}

procedure ULTIMATE.start()
modifies x;
{
    x := 0;
    
    if (true) {
        fork 1 inc();
    }
    else {
        fork 2 dec();
    }
	
	if (true) {
        join 1;
    }
    else {
        join 2;
    }
	
	assert x >= 0;
}