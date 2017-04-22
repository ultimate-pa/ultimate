//#Safe
/*
 *
 */

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
	assert old(x) == x ;	
}
