//#Unsafe

var x : int;

procedure f()
modifies x;
{
    call g();
    x := 7;
	assert x != 7;
}

procedure g() {
    var x : bool;
    x := true;
}

