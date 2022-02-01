/*
* Date: Aug, 2014
* Author: Matthias Heizmann, Betim Musa
* Each error trace has two reasons for infeasibility
* 1. loop was left too early
* 2. value a[42] is 5
* The second reason leads to useful loop invariant, the first reason is easier
* to find for SmtInterpol, but Z3 detects always the second reason.
*/
implementation main() returns ()
{
    var i,p, q, r : int;
    var a : [int]int;
    i := 0;
    while(i <= 1000) {
	i := i + 1;
    }
    a[p] := 5;
    assume p > 41 && p < 43;
    assume q > 41 && q < 43;
    assert a[q] == 5;
}

procedure main() returns ();
