procedure test (ain: int) returns (r:int)
requires ain == 51;
{
	var a : int;
	a := ain;
	r := 0;
	
	while(a > 0){
		while(a < 100){
			if(a % 2 == 0){
				r := r + 2;
			} else {
				r := r + 1;
			}
			a := a + a + 1;
		} 
		r := r + r;
		a := -a - a -a -1;
	}
	assert r == 0;
}