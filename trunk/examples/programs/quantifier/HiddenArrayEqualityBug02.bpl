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
    var p : int;
    var #validBegin : [int]int;


    #valid := #valid[0 := 0];
    #validBegin := #valid;

    call p := #Ultimate.allocOnStack();
    call ULTIMATE.dealloc(p);

    assert #valid == #validBegin;

}


procedure #Ultimate.allocOnStack() returns (#res.base : int);
ensures 0 == old(#valid)[#res.base];
ensures #valid == old(#valid)[#res.base := 1];
modifies #valid;

procedure ULTIMATE.dealloc(~addr.base : int) returns ();
free ensures #valid == old(#valid)[~addr.base := 0];
modifies #valid;

