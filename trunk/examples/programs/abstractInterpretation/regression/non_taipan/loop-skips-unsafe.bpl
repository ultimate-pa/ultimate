//#Unsafe

procedure ULTIMATE.start(){
    var i : int;

    i := 0;
    while (i != 1000)
    {
		assert true;
		assert true;
		i := i +1;
    }
	assert i != 1000;
}
