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

implementation funSelect(n : int, fp : int) returns (res : int){
    if (fp == fourtytwo) {
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
    call x := funSelect(x, twentythree);
    call x := funSelect(x, fourtytwo);
    assert x == 5;
}

const twentythree : int;
axiom twentythree == 23;
const fourtytwo : int;
axiom fourtytwo == 42;

procedure ULTIMATE.start() returns ();
modifies ;

procedure funSelect(n : int, fp : int) returns (res : int);
modifies ;

