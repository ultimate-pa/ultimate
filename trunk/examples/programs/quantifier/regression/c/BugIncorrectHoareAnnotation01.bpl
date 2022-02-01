// #Safe
/* 
 * BoogiePrinter from FunctionPointers01.c
 * "java.lang.AssertionError: incorrect Hoare annotation" with backward predicates
 * 
 * Probably some problem with constant or axiom
 *
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-09-11
 *
 */


implementation ULTIMATE.init() returns (){
}

implementation ULTIMATE.start() returns (){
    var #t~ret4 : int;

    call ULTIMATE.init();
    call #t~ret4 := main();
}

implementation fun~PrimitiveTypeint~TO~PrimitiveTypeint(#in~0 : int, #in~#fp : $Pointer$) returns (#res : int){
    var #~0 : int;
    var #t~funptrres5 : int;
    var #t~ret6 : int;
    var #t~ret7 : int;

    #~0 := #in~0;
    if (#in~#fp == #funAddr~dec) {
        call #t~ret7 := dec(#~0);
        assume -2147483648 <= #t~ret7 && #t~ret7 <= 2147483647;
        #t~funptrres5 := #t~ret7;
    } else {
        call #t~ret6 := inc(#~0);
        assume -2147483648 <= #t~ret6 && #t~ret6 <= 2147483647;
        #t~funptrres5 := #t~ret6;
    }
    #res := #t~funptrres5;
    havoc #t~funptrres5;
    havoc #t~ret6;
    havoc #t~ret7;
    return;
}

implementation inc(#in~x : int) returns (#res : int){
    var ~x : int;

    ~x := #in~x;
    #res := ~x + 1;
    return;
}

implementation dec(#in~x : int) returns (#res : int){
    var ~x : int;

    ~x := #in~x;
    #res := ~x - 1;
    return;
}

implementation main() returns (#res : int){
    var #t~ret1 : int;
    var #t~ret2 : int;
    var #t~ret3 : int;
    var ~y~3 : int;
    var ~func~3 : $Pointer$;

    ~y~3 := 23;
    havoc ~func~3;
    ~func~3 := #funAddr~inc;
    call #t~ret1 := fun~PrimitiveTypeint~TO~PrimitiveTypeint(~y~3, ~func~3);
    assume -2147483648 <= #t~ret1 && #t~ret1 <= 2147483647;
    ~y~3 := #t~ret1;
    havoc #t~ret1;
    call #t~ret2 := fun~PrimitiveTypeint~TO~PrimitiveTypeint(~y~3, ~func~3);
    assume -2147483648 <= #t~ret2 && #t~ret2 <= 2147483647;
    ~y~3 := #t~ret2;
    havoc #t~ret2;
    ~func~3 := #funAddr~dec;
    call #t~ret3 := fun~PrimitiveTypeint~TO~PrimitiveTypeint(~y~3, ~func~3);
    assume -2147483648 <= #t~ret3 && #t~ret3 <= 2147483647;
    ~y~3 := #t~ret3;
    havoc #t~ret3;
    assert ~y~3 == 24;
}

const #funAddr~inc : $Pointer$;
axiom #funAddr~inc == { base: -1, offset: 0 };
const #funAddr~dec : $Pointer$;
axiom #funAddr~dec == { base: -1, offset: 1 };
type $Pointer$ = { base : int, offset : int };
procedure inc(#in~x : int) returns (#res : int);
modifies ;

procedure dec(#in~x : int) returns (#res : int);
modifies ;

procedure main() returns (#res : int);
modifies ;

procedure fun~PrimitiveTypeint~TO~PrimitiveTypeint(#in~0 : int, #in~#fp : $Pointer$) returns (#res : int);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

