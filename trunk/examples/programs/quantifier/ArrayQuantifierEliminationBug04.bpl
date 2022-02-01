implementation f() returns (f : int){
    var #t~mem1 : $Pointer$;

    call #t~mem1 := read~$Pointer$(~pp2~1, 4);
    call write~$Pointer$(#t~mem1, ~pp1~1, 4);
    havoc #t~mem1;
}

implementation main() returns (main : int){
    var #t~ret4 : int;
    var #t~mem7 : $Pointer$;
    var #t~mem8 : int;
    var ~px~3 : $Pointer$;

    havoc ~px~3;
    call write~$Pointer$(~#a~1, ~#p1~1, 4);
    call write~$Pointer$(~#b~1, ~#p2~1, 4);
    ~pp1~1 := ~#p1~1;
    ~pp2~1 := ~#p2~1;
    call #t~ret4 := f();
    call write~int(#t~ret4, ~#a~1, 4);
    havoc #t~ret4;
    call write~int(8, ~#b~1, 4);
    call #t~mem7 := read~$Pointer$(~#p1~1, 4);
    call #t~mem8 := read~int(#t~mem7, 4);
    if (#t~mem8 != 8) {
        havoc #t~mem7;
        havoc #t~mem8;
        if (*) {
            assert false;
        }
    } else {
        havoc #t~mem7;
        havoc #t~mem8;
    }
    main := 0;
    return;
}

var ~#a~1 : $Pointer$;

var ~#b~1 : $Pointer$;

var ~#p1~1 : $Pointer$;

var ~#p2~1 : $Pointer$;

var ~pp1~1 : $Pointer$;

var ~pp2~1 : $Pointer$;

implementation ULTIMATE.init() returns (){
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
    call ~#a~1 := ~malloc(4);
    call write~int(0, ~#a~1, 4);
    call ~#b~1 := ~malloc(4);
    call write~int(0, ~#b~1, 4);
    call ~#p1~1 := ~malloc(4);
    call write~$Pointer$(#NULL, ~#p1~1, 4);
    call ~#p2~1 := ~malloc(4);
    call write~$Pointer$(#NULL, ~#p2~1, 4);
    ~pp1~1 := #NULL;
    ~pp2~1 := #NULL;
}

implementation ULTIMATE.start() returns (){
    var #t~ret9 : int;

    call ULTIMATE.init();
    call #t~ret9 := main();
}

type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };

var #memory_int : [$Pointer$]int;

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
modifies #memory_int, #memory_$Pointer$;

ensures #memory_int == old(#memory_int)[#ptr := #value];

ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
ensures #value == #memory_int[#ptr];

var #memory_$Pointer$ : [$Pointer$]$Pointer$;

procedure write~$Pointer$(#value : $Pointer$, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
modifies #memory_int, #memory_$Pointer$;

ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];

ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #value];

procedure read~$Pointer$(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : $Pointer$);
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

const #sizeof~INT : int;
const #sizeof~$Pointer$ : int;
axiom #sizeof~INT == 4;
axiom #sizeof~$Pointer$ == 4;
procedure __VERIFIER_error() returns ();
modifies ;

procedure f() returns (f : int);
modifies #memory_$Pointer$, #memory_int;

procedure main() returns (main : int);
modifies #memory_$Pointer$, ~pp1~1, ~pp2~1, #memory_int;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL, ~#a~1, ~#b~1, ~#p1~1, ~#p2~1, ~pp1~1, ~pp2~1, #memory_int, #memory_$Pointer$;

modifies #valid, #length, #memory_int, #memory_$Pointer$;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, ~#a~1, ~#b~1, ~#p1~1, ~#p2~1, ~pp1~1, ~pp2~1, #memory_int, #memory_$Pointer$, #memory_$Pointer$, ~pp1~1, ~pp2~1, #memory_int;

modifies #memory_$Pointer$, ~pp1~1, ~pp2~1, #memory_int, #valid, #length;

