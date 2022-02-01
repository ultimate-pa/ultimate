// #Safe
/* Revealed bug in quantifier elimination via TIR.
 * Bug occurred while computing backward predicates.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-05-08
 *
 */


implementation main() returns (#res : int){
    var #t~post2 : int;
    var #t~short4 : bool;
    var x : int;
    var y : int;

    x := 1;
    while (*) {}
	#t~post2 := x;
	x := #t~post2 + 1;
	#t~short4 := #t~post2 != 23;
	if (#t~short4) {
		y := 2;
		#t~short4 := true;
	}
	if (#t~short4) {
		assert x >= 2 && y == 2;
	} 
}

procedure main() returns (#res : int);
modifies ;


