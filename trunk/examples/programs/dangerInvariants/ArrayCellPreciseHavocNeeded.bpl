//#Unsafe
/* Date: 2017-09-20
 * Author: Matthias Heizmann
 * 
 * Program where the DangerInvariantGuesser only finds
 * the danger invariant if we do a cell precise havoc.
 * 
 */

procedure main() {
	var x : int;
	var a : [int]int;
	a[x] := 0;
	while (a[x] < 1000) {
		a[x] := a[x] + 1;
	}
	if (a[0] == 1) {
		assert a[x] != 1000;
	}
}
