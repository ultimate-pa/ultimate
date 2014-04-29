implementation main() returns (#res : int)
{
    var ~#i~1 : $Pointer$;
    var ~p~1 : $Pointer$;

    call ~#i~1 := ~malloc(#sizeof~INT);
    havoc ~p~1;
    call write~int(1, ~#i~1);
    ~p~1 := ~#i~1;
    call ~free(~#i~1);
}

implementation ULTIMATE.init() returns ()
{
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret2 : int;

    call ULTIMATE.init();
    call #t~ret2 := main();
}

type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };
var #memory_$Pointer$ : [$Pointer$]$Pointer$;
procedure write~$Pointer$(#value : $Pointer$, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~$Pointer$ + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #value];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~$Pointer$(#ptr : $Pointer$) returns (#value : $Pointer$);
    requires #valid[#ptr!base];
    requires #sizeof~$Pointer$ + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_$Pointer$[#ptr];

var #memory_int : [$Pointer$]int;
procedure write~int(#value : int, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~INT + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #value];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~int(#ptr : $Pointer$) returns (#value : int);
    requires #valid[#ptr!base];
    requires #sizeof~INT + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_int[#ptr];

var #memory_bool : [$Pointer$]bool;
procedure write~bool(#value : bool, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~BOOL + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #value];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~bool(#ptr : $Pointer$) returns (#value : bool);
    requires #valid[#ptr!base];
    requires #sizeof~BOOL + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_bool[#ptr];

var #memory_real : [$Pointer$]real;
procedure write~real(#value : real, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~REAL + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #value];

procedure read~real(#ptr : $Pointer$) returns (#value : real);
    requires #valid[#ptr!base];
    requires #sizeof~REAL + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_real[#ptr];

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
const #sizeof~$Pointer$ : int;
const #sizeof~BOOL : int;
const #sizeof~REAL : int;
axiom #sizeof~INT > 0;
axiom #sizeof~$Pointer$ > 0;
axiom #sizeof~BOOL > 0;
axiom #sizeof~REAL > 0;
procedure main() returns (#res : int);
    modifies #valid, #length, #memory_int, #memory_$Pointer$, #memory_real, #memory_bool;

procedure ULTIMATE.init() returns ();
    modifies #valid, #NULL;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies #valid, #NULL, #memory_int, #memory_$Pointer$, #memory_real, #memory_bool;
    modifies #valid, #length, #memory_int, #memory_$Pointer$, #memory_real, #memory_bool;

