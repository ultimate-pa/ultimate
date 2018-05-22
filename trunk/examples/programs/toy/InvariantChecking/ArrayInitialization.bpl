//#Safe
/* Multiplication of natural numbers implemented via iterative
 * addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2018-05-08
 */


procedure main() returns (){
	var a : [int]int;
	var n : int;
    var i,j : int;

    assume n >= 0;
	i := 0;
    while (i <= n)
		invariant n >= 0
		&& i >= 0 && i <= n + 1
		&& (j <= i - 1 && j <= n && j >= 0 ==> a[j] == 23);
    {
		a[i] := 23;
		i := i + 1;
    }
    assert j >= 0 && j <= n ==> a[j] == 23;
}

