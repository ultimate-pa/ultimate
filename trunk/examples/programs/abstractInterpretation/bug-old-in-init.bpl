//#Safe
/* Known bug in Ultimate's handling of oldvars: old() is not supported in initial function. 
 *
 */

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
	assert old(x) == x ;	
}
