// #Safe
/*
 * Simplified version of BugIncorrectHoareAnnotation01.bpl
 * "java.lang.AssertionError: incorrect Hoare annotation" with backward predicates
 *
 * Probably some problem with constant or axiom
 *
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2024-08-18
 *
 */


implementation funSelect(n : int, fp : bool) returns (res : int){
    if (fp == trueconst) {
        // break LBE, compute invariant here
        while (*) {}
        res := n - 1;
    } else {
        // break LBE, compute invariant here
        while (*) {}
        res := n + 1;
    }
    return;
}


implementation ULTIMATE.start() returns (){
    var x : int;

    x := 5;
    call x := funSelect(x, false);
    call x := funSelect(x, true);
    assert x == 5;
}

const trueconst : bool;
axiom trueconst == true;


procedure funSelect(n : int, fp : bool) returns (res : int);
modifies ;

procedure ULTIMATE.start() returns ();
modifies ;


