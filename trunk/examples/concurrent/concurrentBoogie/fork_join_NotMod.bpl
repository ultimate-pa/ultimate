//#Safe
/*
 * Check that fork does not accidentally havoc the global variable 
 * globVar or the local variable locVar.
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-09-14
 * 
 */
var globVar : int;


procedure ULTIMATE.start();
modifies globVar;

implementation ULTIMATE.start()
{
	var locVar : int;	
	var x : int;
	globVar := 0;
	locVar := 7;

	fork locVar increment(globVar);
	assert globVar == 0;
	assert locVar == 7;
	join locVar assign x;
	assert globVar == 0;
	assert locVar == 7;
}

procedure increment(n : int) returns(res : int);
modifies globVar;

implementation increment(n : int) returns(res : int)
{
	res := n + 1;
}
