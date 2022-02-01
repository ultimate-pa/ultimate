//#Terminating
/* Example where we obtain an incorrect ranking function in 12732.
 * Example was obtained from a modified version of joey_false-termination.c
 * 
 * Problem: Same auxvar was used for all mod and div during RewriteDivision.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 25.10.2014
 *
 */

procedure main() returns (){
	var y: int;
	while (*) {
		assume (y >= 1);
		assume (y % 2 == 0);
		y := (y % 4294967296) / 2;
	}
}
