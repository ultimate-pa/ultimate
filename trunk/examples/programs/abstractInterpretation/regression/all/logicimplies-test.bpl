//#Safe

procedure ULTIMATE.start()
{
	var input : int;
	var result1 : int;
	var result2 : int;

	call result1 := foo(input);
	call result2 := foo(input);

	assert(input == 0 ==> result1 == 10);
	assert(input == 1 ==> result2 == 20);

}

procedure foo(a : int) returns (res : int)
{
	var bla : int;
	bla := a;

	if (bla == 0)
	{
		res := 10;
		return;
	}

	res := 20;
	return;
}
