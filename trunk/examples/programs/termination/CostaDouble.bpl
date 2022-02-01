//#terminating
/*
 * 2015-07-30, Matthias Heizmann
 * reveals bug in automata library. 
 * symptom: wrong result in buchi difference operations
 *
 * Simplified version of the Double.jar java program contained in a benchmark 
 * suite of the COSTA tool. Translated to Boogie by Joogie.
 */

procedure rec(k : int) {
var y : int;
Block17:
	 //  @line: 14
	y := 0;
	 goto Block18;
	 //  @line: 14
Block18:
	 goto Block21, Block19;
	 //  @line: 14
Block21:
	 //  @line: 14
	 assume (y < k);
	 //  @line: 15
	 call rec((y));
	 //  @line: 14
	y := y + 1;
	 goto Block18;
	 //  @line: 14
Block19:
	 assume (y >= k);
	 goto Block20;
	 //  @line: 16
Block20:
	 return;
}
