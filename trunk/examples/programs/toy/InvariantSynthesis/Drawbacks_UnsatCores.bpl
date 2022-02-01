//#Safe
/* * 
	Author: musab@informatik.uni-freiburg.de
	
	The usage of unsat cores in invariant synthesis has 2 drawbacks:
	(a) the template of a location may be too much increased, if it is too often in unsat core, i.e. a smaller templates are also sufficient
	(b) the idea of only increasing the templates at the locations which are in the unsat core of the previous round may lead to the execution
	of too many rounds. 
	
	This example shows (mainly) the second drawback.
	> Using the classical variant of invariant synthesis we need only two rounds to verify it, because after the first round we increase
	template at every location to 2 conjuncts.
	> Using the help of unsat cores during invariant synthesis, we need 6 rounds to verify it
 */

var a, x, y, z, b, c : int;
  
procedure main()
modifies a, x, y, z, b, c;
{
	z := 0;
	x := 42;
	while (*) {
	}
	b := z;
	while (*) {
	}
	c := b;
	y := x;
	while (*) {
	}
	z := y;
	assert (c <= 0 && z <= 42);
} 
