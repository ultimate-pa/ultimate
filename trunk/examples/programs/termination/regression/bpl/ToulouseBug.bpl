//#Terminating
/*
 * Date: 2015-08-09
 * Author: Matthias Heizmann
 * 
 * Simplified version obtained from
 * svcomp/termination-memory-alloca/Toulouse-BranchesToLoop-alloca_true-termination.c.i
 * I used this example to analyse the bug that was fixed in r14863
 * (bugfix: fresh auxiliary variable for each store)
 * The bug is only(?) reproduceable if you use the BlockEncoding plugin.
 * After 14906 this bug can be detected if you enable the flag in RewriteArrays
 * that does additional checks if assertions are enabled.
 */

implementation main() returns (#res : int){
    var #t~malloc0 : $Pointer$;
    var #t~malloc1 : $Pointer$;
    var #t~malloc2 : $Pointer$;
    var #t~malloc3 : $Pointer$;
    var #t~malloc4 : $Pointer$;
    var #t~nondet5 : int;
    var #t~mem11 : int;
    var #t~mem12 : int;
    var #t~mem14 : int;
    var #t~mem15 : int;
    var #t~mem8 : int;
    var #t~mem9 : int;
    var #t~short10 : bool;
    var x : $Pointer$;
    var y : $Pointer$;
    var ~z~2 : $Pointer$;
    var ~m~2 : $Pointer$;
    var ~n~2 : $Pointer$;

    call #t~malloc0 := ~malloc(4);
    x := #t~malloc0;
    call #t~malloc1 := ~malloc(4);
    y := #t~malloc1;
    call #t~malloc2 := ~malloc(4);
    ~z~2 := #t~malloc2;
    call #t~malloc3 := ~malloc(4);
    ~m~2 := #t~malloc3;
    call #t~malloc4 := ~malloc(4);
    ~n~2 := #t~malloc4;
    if (*) {
        call write~int(1, x, 4);
    } else {
        call write~int(-1, x, 4);
    }
    while (true)
    {
      Loop~0:
        call #t~mem8 := read~int(y, 4);
        #t~short10 := #t~mem8 < 100;
        if (#t~short10) {
            call #t~mem9 := read~int(~z~2, 4);
            #t~short10 := #t~mem9 < 100;
        }
        if (!#t~short10) {
            havoc #t~mem8;
            havoc #t~mem9;
            havoc #t~short10;
            break;
        } else {
            havoc #t~mem8;
            havoc #t~mem9;
            havoc #t~short10;
        }
        call #t~mem11 := read~int(y, 4);
        call #t~mem12 := read~int(x, 4);
        call write~int(#t~mem11 + #t~mem12, y, 4);
        havoc #t~mem11;
        havoc #t~mem12;
        call #t~mem14 := read~int(~z~2, 4);
        call #t~mem15 := read~int(x, 4);
        call write~int(#t~mem14 - #t~mem15, ~z~2, 4);
        havoc #t~mem14;
        havoc #t~mem15;
    }
    #res := 0;
    call ~free(#t~malloc0);
    havoc #t~malloc0;
    call ~free(#t~malloc1);
    havoc #t~malloc1;
    call ~free(#t~malloc2);
    havoc #t~malloc2;
    call ~free(#t~malloc3);
    havoc #t~malloc3;
    call ~free(#t~malloc4);
    havoc #t~malloc4;
    return;
    call ~free(#t~malloc0);
    havoc #t~malloc0;
    call ~free(#t~malloc1);
    havoc #t~malloc1;
    call ~free(#t~malloc2);
    havoc #t~malloc2;
    call ~free(#t~malloc3);
    havoc #t~malloc3;
    call ~free(#t~malloc4);
    havoc #t~malloc4;
}

implementation ULTIMATE.init() returns (){
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
}

implementation ULTIMATE.start() returns (){
    var #t~ret17 : int;

    call ULTIMATE.init();
    call #t~ret17 := main();
}

type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };

var #memory_int : [$Pointer$]int;

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
requires #valid[#ptr!base];
requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];
modifies #memory_int;
ensures #memory_int == old(#memory_int)[#ptr := #value];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
requires #valid[#ptr!base];
requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];
ensures #value == #memory_int[#ptr];

var #valid : [int]bool;

var #length : [int]int;

procedure ~free(~addr : $Pointer$) returns ();
requires ~addr!offset == 0;
requires #valid[~addr!base];
ensures #valid == old(#valid)[~addr!base := false];
modifies #valid;

procedure ~malloc(~size : int) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == false;
ensures #valid == old(#valid)[#res!base := true];
ensures #res!offset == 0;
ensures #res!base != 0;
ensures #length == old(#length)[#res!base := ~size];
modifies #valid, #length;

const #sizeof~INT : int;
axiom #sizeof~INT == 4;
procedure __VERIFIER_nondet_int() returns (#res : int);
modifies ;

procedure main() returns (#res : int);
modifies #memory_int, #valid, #length;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL;
modifies ;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, #memory_int;
modifies #valid, #length, #memory_int;

