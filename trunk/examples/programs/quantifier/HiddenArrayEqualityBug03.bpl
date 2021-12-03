//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2021-11-15
 * 
 * Reveals bug in quantifier elimination for arrays.
 * After the bug is fixed, we can probably only keep the smallest of
 * the three examples.
 */

var #valid : [int]int;

procedure ULTIMATE.start() returns ();
modifies #valid;

implementation ULTIMATE.start() returns (){
    var #validOld : [int]int;

    #valid := #valid[1000 := 1001];
    #validOld := #valid;
    assume 42 == #valid[23];
    #valid := #valid[23 := 42];
    assert #valid == #validOld;
}

