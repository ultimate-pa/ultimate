// Example where we obtain an incorrect ranking function in 12732.
// Example was obtained from a modified version of joey_false-termination.c


implementation rec(#in~x : int) returns (rec : int){
    var #t~ret0 : int;
    var ~x : int;

    ~x := #in~x;
    if (~x <= 0) {
        rec := ~x;
        return;
    } else if (~x % 2 == 0) {
        call #t~ret0 := rec(~x % 4294967296 / 2);
        rec := #t~ret0;
        havoc #t~ret0;
        return;
    }
}

implementation main() returns (main : int){
    var #t~nondet1 : int;
    var #t~ret2 : int;
    var ~x~5 : int;

    ~x~5 := #t~nondet1;
    havoc #t~nondet1;
    call #t~ret2 := rec(~x~5);
    havoc #t~ret2;
}

implementation ULTIMATE.init() returns (){
}

implementation ULTIMATE.start() returns (){
    var #t~ret3 : int;

    call ULTIMATE.init();
    call #t~ret3 := main();
}

procedure __VERIFIER_nondet_int() returns (#res : int);
modifies ;

procedure rec(#in~x : int) returns (rec : int);
modifies ;

procedure main() returns (main : int);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ;

modifies ;

procedure ULTIMATE.start() returns ();
modifies ;

modifies ;

