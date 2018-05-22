//#Safe
/* Example obtained from simplifying the SV-COMP benchmark
 *     loop-new/count_by_1_variant_true-unreach-call.i
 * Reveals a bug in InterpolantConsolidation. 
 *     java.lang.AssertionError: invalid Hoare triple in CP
 * Bug can be reproduced using BackwardPredicates (not FPandBP).
 * 
 * Author: Matthias Heizmann
 * Date: 2016-01-06
 */


procedure main() returns (){
    var i : int;
    var x : int;

    i := 0;
    while (i != 1000000)
		invariant i < 1000000;
    {
        x := (if i <= 1000000 then 1 else 0);
        assert (x != 0);
        i := i + 1;
    }
}

