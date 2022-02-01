//#Safe
/*
 * Shows bug in backward predicates. It seems like procedure summaries 
 * are not computed with respect to the unsat core.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-12-15
 *
 */




procedure main(x : int) returns (ret : bool)
{
	var y : int;
	var verum : bool;
	
	if(*) {
		assume (y == 0);
	} else {
		assume (y >= 1);
	}
	call verum := alwaysTrue(y);
	assert (verum);
}

procedure alwaysTrue(z : int) returns (ret : bool)
{
	var CallRet : bool;
	
	
	call isZero(z);
	call ret := notZero(z);
}

procedure isZero(x : int) returns ()
{
	assume (x != 0);
}

procedure notZero(x : int) returns (ret : bool)
{
	if (x != 0) {
		ret := true;
	} 
}