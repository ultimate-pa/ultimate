// #Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-07-21
 */
procedure main() {
	var x : int;
	x := 0;
	if (*) {
		goto $l2$l2;
	} else {
		x := 1;
		goto endend;
	}
	x := 2;
	$l2$l7: if (*) {
		x := 3;
		goto endend;
	} 

	$l2$l2: if (*) {
		x := 4;
		assert false;
	} 
	endend:
}
