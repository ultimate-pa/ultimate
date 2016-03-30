//#Safe
/*
 * Tests disjunctive states
 */

procedure ULTIMATE.start()
{
	var x : int;

	if(*){
		x := 1;
	}else{
		x := -1;
	}
	
	if(*){
		x := 1;
	}else{
		x := -1;
	}

	x := x * 2;
	assert x != 0 ;
}
