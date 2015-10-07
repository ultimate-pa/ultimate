//#Safe
/*
 * Author: ???
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x: int;
	
	havoc x;	
	x := 0;
	
	assert (x < 1);
}