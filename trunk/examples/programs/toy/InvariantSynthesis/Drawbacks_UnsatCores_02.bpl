//#Safe
/* * 
	Author: heizmann@informatik.uni-freiburg.de, musab@informatik.uni-freiburg.de 
	This is a nicely parametrized (by the number of loops) example that reveals the weakness of unsat core usage in invariant synthesis.
	Using unsat cores in invariant synthesis one needs n + 1 rounds to verify it, where n the number of loops.
	Using the classical variant of invariant synthesis one needs only 2 rounds to verify it.
 */

var x: int;
  
procedure main()
modifies x;
{
	x := 0;
	while (*) {}
	while (*) {}
	while (*) {}
	while (*) {}
	assert x == 0;
} 
