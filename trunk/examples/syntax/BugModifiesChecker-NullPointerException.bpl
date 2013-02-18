#iSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 01.04.2012
 * 
 * Reduced version of Jeremis and Vincents nonTermination_TRE.bpl
 * 
 * Using StrongesPost determinizer the Hoare Annotation is not inductive 
 *
 */




procedure Test()
{
        var ret: bool;
        call ret:= nonTermination(0);

	assert(false);
}

procedure nonTermination(x : int) returns (ret : bool)
{
	var blockCall : bool;
	assume x == 0;
	while (true) 
	{
		call blockCall := test();
		if (!blockCall) { ret := false; return; }

	}
}