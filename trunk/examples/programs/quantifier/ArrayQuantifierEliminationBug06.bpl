//#Safe
// Date: 2014-01-27
// Author: Matthias Heizmann
// Reveals bug in quantifier elimination up to revision 13376.
// Using DER we replaced for the term ∃x (a[x] == x) the variable x by a[x]
// although, a[x] contains x itself.

implementation check(#in~ad1 : $Pointer$, #in~b : int) returns (#res : int){
    var #t~mem0 : int;
    var ~ad1 : $Pointer$;
    var ~b : int;

    ~ad1 := #in~ad1;
    ~b := #in~b;
    call #t~mem0 := read~int({ base: ~ad1!base, offset: ~ad1!offset + ~b * 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    #res := (if #t~mem0 == ~b then 1 else 0);
    havoc #t~mem0;
    return;
}

implementation main() returns (#res : int){
    var #t~nondet1 : [int]{ a : int, b : int };
    var #t~mem24 : int;
    var #t~post26 : int;
    var #t~mem25 : int;
    var #t~ret27 : int;
    var ~#ad1~5 : $Pointer$;
    var ~ad2~5 : $Pointer$;
    var ~i~5 : int;
    var ~pa~5 : $Pointer$;

    call ~#ad1~5 := ~malloc(80);
    call write~int(#t~nondet1[0]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[0]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[1]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[1]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[2]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[2]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[3]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[3]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[4]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[4]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[5]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[5]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[6]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[6]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[7]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[7]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[8]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[8]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    call write~int(#t~nondet1[9]!a, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
    call write~int(#t~nondet1[9]!b, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + #offset~STRUCT#?a~INT?b~INT#~b }, 4);
    havoc ~ad2~5;
    havoc #t~nondet1;
    havoc ~i~5;
    havoc ~pa~5;
    if (~i~5 >= 0 && ~i~5 < 10) {
        ~ad2~5 := ~#ad1~5;
        call write~int(~i~5, { base: ~#ad1~5!base, offset: ~#ad1~5!offset + ~i~5 * 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
        ~pa~5 := { base: ~#ad1~5!base, offset: ~#ad1~5!offset + ~i~5 * 8 + #offset~STRUCT#?a~INT?b~INT#~a };
        call #t~mem24 := read~int({ base: ~ad2~5!base, offset: ~ad2~5!offset + ~i~5 * 8 + #offset~STRUCT#?a~INT?b~INT#~a }, 4);
        ~i~5 := #t~mem24 - 10;
        havoc #t~mem24;
        while (true)
        {
            call #t~mem25 := read~int(~pa~5, 4);
          Loop~0:
            if (!(~i~5 < #t~mem25)) {
                havoc #t~mem25;
                break;
            } else {
                havoc #t~mem25;
            }
            #t~post26 := ~i~5 + 1;
            ~i~5 := #t~post26;
            havoc #t~post26;
        }
        call #t~ret27 := check(~#ad1~5, ~i~5);
        if (!(#t~ret27 != 0)) {
            havoc #t~ret27;
            call assert_fail();
            goto ERROR;
        } else {
            havoc #t~ret27;
        }
    }
    #res := 0;
    call ~free(~#ad1~5);
    havoc ~#ad1~5;
    return;
  ERROR:
    #res := 1;
    call ~free(~#ad1~5);
    havoc ~#ad1~5;
    return;
    call ~free(~#ad1~5);
    havoc ~#ad1~5;
}

implementation ULTIMATE.init() returns (){
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
}

implementation ULTIMATE.start() returns (){
    var #t~ret28 : int;

    call ULTIMATE.init();
    call #t~ret28 := main();
}

function #to_int(real) returns (outInt : int);
type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };

var #memory_int : [$Pointer$]int;

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];

modifies #memory_int, #memory_$Pointer$;

ensures #memory_int == old(#memory_int)[#ptr := #value];

ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];

ensures #value == #memory_int[#ptr];

var #memory_$Pointer$ : [$Pointer$]$Pointer$;

procedure write~$Pointer$(#value : $Pointer$, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];

modifies #memory_int, #memory_$Pointer$;

ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];

ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #value];

procedure read~$Pointer$(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : $Pointer$);
requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];

ensures #value == #memory_$Pointer$[#ptr];

var #valid : [int]bool;

var #length : [int]int;

procedure ~free(~addr : $Pointer$) returns ();
procedure ~malloc(~size : int) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == false;

ensures #valid == old(#valid)[#res!base := true];

ensures #res!offset == 0;

ensures #res!base != 0;

ensures #length == old(#length)[#res!base := ~size];

modifies #valid, #length;

const #offset~STRUCT#?a~INT?b~INT#~a : int;
const #offset~STRUCT#?a~INT?b~INT#~b : int;
const #sizeof~INT : int;
const #sizeof~$Pointer$ : int;
axiom #offset~STRUCT#?a~INT?b~INT#~a == 0;
axiom #offset~STRUCT#?a~INT?b~INT#~b == 4;
axiom #sizeof~INT == 4;
axiom #sizeof~$Pointer$ == 4;
procedure __VERIFIER_error() returns ();
modifies ;

procedure printf(#in~format : $Pointer$) returns ();
modifies ;

procedure assert_fail() returns ();
modifies ;

procedure check(#in~ad1 : $Pointer$, #in~b : int) returns (#res : int);
modifies ;

procedure main() returns (#res : int);
modifies #memory_$Pointer$, #memory_int, #valid, #length;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL;

modifies ;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, #memory_$Pointer$, #memory_int;

modifies #valid, #length, #memory_$Pointer$, #memory_int;

