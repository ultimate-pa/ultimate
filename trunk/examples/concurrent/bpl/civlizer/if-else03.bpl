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

    // interference from inc is possible

	  if (c) {
        join 1;
    }
    
    // no interference from inc is possible
	
	  assert x == 1 || x == 0;
}
