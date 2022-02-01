//#Safe
/* Multiplication of natural numbers implemented via iterative
 * addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2016-01-06
 */


procedure main() returns (){
    var n,m,n_tmp,result : int;
    var x : int;

    assume n >= 0;
	assume m >= 0;
	n_tmp := n;
	result := 0;
    while (n_tmp >= 1)
		invariant result == (n-n_tmp) * m
		&& n >=0 && m >=0 && n_tmp <= n && n_tmp >=0;
    {
		result := result + m;
		n_tmp := n_tmp - 1;
    }
    assert result == n * m;
}

