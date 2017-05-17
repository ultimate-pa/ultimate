//#Unsafe
/*
	28.4.2017 
	Old Statement Bug in Abstract interpretation 
	Old value not carried over by octagons 

*/ 

var x : int;

procedure ULTIMATE.start() returns ()
modifies x;
{
    var i : int;
	x := 0;
	 
    i := 0;
    while (true)
    {
        if (i < 4) {
        } else {
            call foo();
			return;
        }
        i := i + 1;
    }
}

procedure foo() returns ()
modifies x;
{
    x := 1;
    call fail();
}


procedure fail() returns (){
    assert false;
}
