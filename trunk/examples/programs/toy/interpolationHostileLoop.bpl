//#Safe
/*
 * Date: 14.02.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Right now we can not prove correctness using interpolation.
 * Each error trace is infeasible because of two reasons.
 * 1. x := 23 , ...., x !=23 is infeasible
 * 2. i:=0, n:=100, i++, i++ i<=n is infeasible.
 * 
 * Unfortunately we always consider the second reason and fail to obtain the
 * useful predicate x==23.
 * 
 */
 
var x : int;
var i : int;
var n : int;

implementation main() returns ()
{


    x := 23;
    i := 0;
    n := 100;
    while (i < n)
    {
        i := i + 1;
    }
    assert x == 23;
}

procedure main() returns ();
    modifies x, i, n;

