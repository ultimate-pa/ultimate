//#Safe
/* 
 * Program from Exercise 01 of Sheet 09 in the lecture on program verification.
 * https://swt.informatik.uni-freiburg.de/teaching/SS2020/program-verification
 * 
 * Author: Matthias Heizmann
 * Date: 2018-05-28
 */


procedure main(i,j : int) returns (x,y : int)
requires true;
ensures (i == j) ==> (y == 0);
{
	x := i;
	y := j;
    while (x != 0)
		invariant ((i==j) ==> (x == y));
// 		invariant (x-y)==(i-j);
    {
		x := x - 1;
		y := y - 1;
    }
}
