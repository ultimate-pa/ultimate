//#Safe
/* 
 * Program from Exercise 4 of Sheet 4 in the lecture on program verification.
 * https://swt.informatik.uni-freiburg.de/teaching/SS2018/program-verification/program-verification
 * 
 * Author: Matthias Heizmann
 * Date: 2018-05-28
 */


procedure main() returns (){
    var x,y,i,j : int;

    assume true;
	x := i;
	y := j;
    while (x != 0)
		invariant ((i==j) ==> (x == y));
// 		invariant (x-y)==(i-j);
    {
		x := x - 1;
		y := y - 1;
    }
    assert (i == j) ==> (y == 0);
}
