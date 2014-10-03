procedure test (a: int) returns (r:int)
{
	if(a > 10){
		if(a < 100){
			r := 1;
		} else{
			r := 2;
		}
	} else{
		if(a < 5){
			r := 3;
		} else {
			r := 4;
		}
	}
	assert r != 3;
}