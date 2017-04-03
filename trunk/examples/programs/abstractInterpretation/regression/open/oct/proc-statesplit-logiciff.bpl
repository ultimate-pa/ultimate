//#Safe

procedure ULTIMATE.start()
{
	var input : int;
	var result : int;

	call result := foo(input);
	
	assert(input < 0 <==> result != 20);
}

procedure foo(a : int) returns (res : int)
{
	if (a < 0){
		res := 10;
	} else {
		res := 20;
	}
}