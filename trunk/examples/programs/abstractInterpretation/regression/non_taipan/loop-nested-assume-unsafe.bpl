//#Unsafe

procedure ULTIMATE.start(){
    var i : int;

    i := 0;
    while (true)
    {
        if (i == 1000000) {
            break;
        }
		call foo(i <= 1000000);
		i := i + 1;
    }
	assert false;
}


procedure foo(j : bool){
	assert j;
}