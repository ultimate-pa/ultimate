//#Nonterminating
/*
 * Date: 2016-09-06
 * Author: Matthias Heizmann
 * 
 * Shows bug in new map elimination:
 * java.lang.AssertionError: inconsistent lasso after RewriteArraysMapElimination: allAreInOutAux
 * Some auxvar is not in the set of auxvars
 * 
 */



implementation ULTIMATE.start() returns (){
    var #t~ret2 : int;

    call #t~ret2 := main();
}

implementation bubblesort() returns (){
    while (true)
    {
    }
}

implementation main() returns (#res : int){
    var #t~malloc1 : int;
    var ~n~4 : int;

    call #t~malloc1 := #Ultimate.alloc(~n~4 * 4);
    call bubblesort();
}

var #valid : [int]int;


procedure #Ultimate.alloc(~size : int) returns (#res : int);
ensures old(#valid)[#res] == 0;
ensures #valid == old(#valid)[#res := 1];
modifies #valid;

procedure bubblesort() returns ();
modifies ;

procedure main() returns (#res : int);
modifies #valid;


procedure ULTIMATE.start() returns ();
modifies #valid;

