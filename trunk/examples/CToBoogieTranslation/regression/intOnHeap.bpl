implementation main() returns (#res : int)
{
    var ~ip~1.base : int, ~ip~1.offset : int;
    var ~#i~1.base : int, ~#i~1.offset : int;

  $Ultimate##0:
    ~ip~1.base, ~ip~1.offset := ~#i~1.base, ~#i~1.offset;
    return;
}

implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    #NULL.base, #NULL.offset := 0, 0;
    #valid := #valid[0 := false];
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret1 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret1 := main();
    return;
}

var #NULL.base : int, #NULL.offset : int;
var #memory_$Pointer$.base : [int,int]int, #memory_$Pointer$.offset : [int,int]int;
procedure write~$Pointer$(#value.base : int, #value.offset : int, #ptr.base : int, #ptr.offset : int) returns ();
    modifies #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$.base == old(#memory_$Pointer$.base)[#ptr.base,#ptr.offset := #value.base] && #memory_$Pointer$.offset == old(#memory_$Pointer$.offset)[#ptr.base,#ptr.offset := #value.offset];
    ensures #memory_int == old(#memory_int)[#ptr.base,#ptr.offset := #memory_int[#ptr.base,#ptr.offset]];
    ensures #memory_bool == old(#memory_bool)[#ptr.base,#ptr.offset := #memory_bool[#ptr.base,#ptr.offset]];
    ensures #memory_real == old(#memory_real)[#ptr.base,#ptr.offset := #memory_real[#ptr.base,#ptr.offset]];

procedure read~$Pointer$(#ptr.base : int, #ptr.offset : int) returns (#value.base : int, #value.offset : int);
    ensures #value.base == #memory_$Pointer$.base[#ptr.base,#ptr.offset] && #value.offset == #memory_$Pointer$.offset[#ptr.base,#ptr.offset];

var #memory_int : [int,int]int;
procedure write~int(#value : int, #ptr.base : int, #ptr.offset : int) returns ();
    modifies #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$.base == old(#memory_$Pointer$.base)[#ptr.base,#ptr.offset := #memory_$Pointer$.base[#ptr.base,#ptr.offset]] && #memory_$Pointer$.offset == old(#memory_$Pointer$.offset)[#ptr.base,#ptr.offset := #memory_$Pointer$.offset[#ptr.base,#ptr.offset]];
    ensures #memory_int == old(#memory_int)[#ptr.base,#ptr.offset := #value];
    ensures #memory_bool == old(#memory_bool)[#ptr.base,#ptr.offset := #memory_bool[#ptr.base,#ptr.offset]];
    ensures #memory_real == old(#memory_real)[#ptr.base,#ptr.offset := #memory_real[#ptr.base,#ptr.offset]];

procedure read~int(#ptr.base : int, #ptr.offset : int) returns (#value : int);
    ensures #value == #memory_int[#ptr.base,#ptr.offset];

var #memory_bool : [int,int]bool;
procedure write~bool(#value : bool, #ptr.base : int, #ptr.offset : int) returns ();
    modifies #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$.base == old(#memory_$Pointer$.base)[#ptr.base,#ptr.offset := #memory_$Pointer$.base[#ptr.base,#ptr.offset]] && #memory_$Pointer$.offset == old(#memory_$Pointer$.offset)[#ptr.base,#ptr.offset := #memory_$Pointer$.offset[#ptr.base,#ptr.offset]];
    ensures #memory_int == old(#memory_int)[#ptr.base,#ptr.offset := #memory_int[#ptr.base,#ptr.offset]];
    ensures #memory_bool == old(#memory_bool)[#ptr.base,#ptr.offset := #value];
    ensures #memory_real == old(#memory_real)[#ptr.base,#ptr.offset := #memory_real[#ptr.base,#ptr.offset]];

procedure read~bool(#ptr.base : int, #ptr.offset : int) returns (#value : bool);
    ensures #value == #memory_bool[#ptr.base,#ptr.offset];

var #memory_real : [int,int]real;
procedure write~real(#value : real, #ptr.base : int, #ptr.offset : int) returns ();
    modifies #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$.base == old(#memory_$Pointer$.base)[#ptr.base,#ptr.offset := #memory_$Pointer$.base[#ptr.base,#ptr.offset]] && #memory_$Pointer$.offset == old(#memory_$Pointer$.offset)[#ptr.base,#ptr.offset := #memory_$Pointer$.offset[#ptr.base,#ptr.offset]];
    ensures #memory_int == old(#memory_int)[#ptr.base,#ptr.offset := #memory_int[#ptr.base,#ptr.offset]];
    ensures #memory_bool == old(#memory_bool)[#ptr.base,#ptr.offset := #memory_bool[#ptr.base,#ptr.offset]];
    ensures #memory_real == old(#memory_real)[#ptr.base,#ptr.offset := #value];

procedure read~real(#ptr.base : int, #ptr.offset : int) returns (#value : real);
    ensures #value == #memory_real[#ptr.base,#ptr.offset];

var #valid : [int]bool;
var #length : [int]int;
procedure ~free(~addr.base : int, ~addr.offset : int) returns ();

procedure ~malloc(~size : int) returns (#res.base : int, #res.offset : int);
    ensures old(#valid)[#res.base] == false;
    ensures #valid == old(#valid)[#res.base := true];
    ensures #res.offset == 0;
    ensures #res.base != 0;
    ensures #length == old(#length)[#res.base := ~size];
    modifies #valid, #length;

const #sizeof~$Pointer$ : int;
const #sizeof~INT : int;
const #sizeof~BOOL : int;
const #sizeof~REAL : int;
axiom #sizeof~$Pointer$ > 0;
axiom #sizeof~INT > 0;
axiom #sizeof~BOOL > 0;
axiom #sizeof~REAL > 0;
procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies #valid, #NULL.base, #NULL.offset;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies #valid, #NULL.base, #NULL.offset;
    modifies ;

