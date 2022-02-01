//#Safe
/*
 * AssertionError: isSubsetOf unsound 
 * Facts 
 * Happens when disjunctive state is checked for subset relation 
 * c isSubsetOrEqual a || b
 * where a || b <=> true / TOP and c <=> true/TOP 
 * e.g. x > 1 || x <= 1 isSubsetOrEqual true 
 * current check tries to resolve disjunction by checking x > 1 isSubsetOrEqual true || x<= 1 isSubsetOrEqual true 
 * Options: 
 * change algorithm (how?)
 * change assertion (easier) 
 * ??? 
 * Minimal example 
 */
 

procedure hanoi(#in~n : int) returns (#res : int){
    var #t~ret0 : int;
    var ~n : int;

    ~n := #in~n;
    if (~n == 1) {
        #res := 1;
        return;
    }
    call #t~ret0 := hanoi(1);
    #res := 2 * #t~ret0;
    havoc #t~ret0;
    return;
}

procedure ULTIMATE.start() returns (){
    var t : int;
    var n : int;
    var r : int;

    n := t;
    havoc t;
    if (false) {
    }
    call r := hanoi(n);


    if (r != 0) {
    } else {
        assert false;
    }
}
