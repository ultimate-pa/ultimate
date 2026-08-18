
var x : int;

procedure inc() returns()
modifies x;
{
	x := x + 1;
}

procedure dec() returns()
modifies x;
{
	x := x - 1;
}

procedure ULTIMATE.start()
modifies x;
{
    var c : bool;
    x := 0;
    
    if (c) {
        fork 1 inc();
    }
    else {
        fork 2 dec();
    }
	
	if (c) {
        join 1;
    }
    else {
        join 2;
    }
	
	assert x == 1 || x == -1;
}