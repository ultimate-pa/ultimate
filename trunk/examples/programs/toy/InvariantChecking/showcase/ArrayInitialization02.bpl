//#Safe
/* Initialize array from 0 to n with the integer 23
 * and checks for some j\in{0,...,n} if a[j] is indeed 23.
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
		&& (forall k: int :: 0 <= k && k <= i - 1 ==> a[k] == 23);
    {
		a[i] := 23;
		i := i + 1;
    }
    assert j >= 0 && j <= n ==> a[j] == 23;
}

