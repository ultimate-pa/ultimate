//#Safe

procedure ULTIMATE.start()
{
	var input : int;
	var result : int;

	if (input < 0){
		result := 10;
	} else {
		result := 20;
	}
	
	assert(input < 0 <==> result != 20);
}
