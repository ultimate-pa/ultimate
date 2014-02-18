implementation main() returns (#res : int)
{
    var ~p~1.base : int, ~p~1.offset : int;
    var ~j~1 : int;
    var ~#i~1.base : int, ~#i~1.offset : int;
    var #t~mem0 : int;
    var #t~mem2 : int;

  $Ultimate##0:
    ~p~1.base, ~p~1.offset := ~#i~1.base, ~#i~1.offset;
    call #t~mem0 := read~int(~#i~1.base, ~#i~1.offset + 2 * #sizeof~INT);
    ~j~1 := #t~mem0;
    havoc #t~mem0;
    call write~int(1, ~#i~1.base, ~#i~1.offset + 0 * #sizeof~INT);
    call #t~mem2 := read~int(~p~1.base, ~p~1.offset + 2 * #sizeof~INT);
    call write~int(#t~mem2 + 4, ~#i~1.base, ~#i~1.offset + 1 * #sizeof~INT);
    havoc #t~mem2;
    ~mdga := ~mdga[1,2,0 := 4];
    ~j~1 := ~mdga[1,2,0];
    ~mdgaHp.base, ~mdgaHp.offset := ~mdgaH.base, ~mdgaH.offset;
    return;
}

var ~ga : [int]int;
var ~pga.base : int, ~pga.offset : int;
var ~mdga : [int,int,int]int;
var ~mdgaH.base : int, ~mdgaH.offset : int;
var ~mdgaHp.base : int, ~mdgaHp.offset : int;
implementation ULTIMATE.init() returns ()
{
    var #t~init4.base : int, #t~init4.offset : int;

  $Ultimate##0:
    #NULL.base, #NULL.offset := 0, 0;
    #valid := #valid[0 := false];
    ~ga := ~ga[0 := 0];
    ~ga := ~ga[1 := 0];
    ~ga := ~ga[2 := 0];
    ~ga := ~ga[3 := 0];
    ~ga := ~ga[4 := 0];
    ~pga.base, ~pga.offset := #NULL.base, #NULL.offset;
    ~mdga := ~mdga[0,0,0 := 0];
    ~mdga := ~mdga[0,1,0 := 0];
    ~mdga := ~mdga[0,2,0 := 0];
    ~mdga := ~mdga[1,0,0 := 0];
    ~mdga := ~mdga[1,1,0 := 0];
    ~mdga := ~mdga[1,2,0 := 0];
    call #t~init4.base, #t~init4.offset := ~malloc(#sizeof~ARRAY#_2_3_~INT#);
    ~mdgaH.base, ~mdgaH.offset := #t~init4.base, #t~init4.offset;
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 0 * (3 * #sizeof~INT) + 0 * #sizeof~INT);
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 0 * (3 * #sizeof~INT) + 1 * #sizeof~INT);
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 0 * (3 * #sizeof~INT) + 2 * #sizeof~INT);
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 1 * (3 * #sizeof~INT) + 0 * #sizeof~INT);
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 1 * (3 * #sizeof~INT) + 1 * #sizeof~INT);
    call write~int(0, ~mdgaH.base, ~mdgaH.offset + 1 * (3 * #sizeof~INT) + 2 * #sizeof~INT);
    ~mdgaHp.base, ~mdgaHp.offset := #NULL.base, #NULL.offset;
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret5 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret5 := main();
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

const #sizeof~INT : int;
const #sizeof~ARRAY#_2_3_~INT# : int;
const #sizeof~$Pointer$ : int;
const #sizeof~BOOL : int;
const #sizeof~REAL : int;
axiom #sizeof~INT > 0;
axiom #sizeof~ARRAY#_2_3_~INT# > 0;
axiom #sizeof~ARRAY#_2_3_~INT# == 1 * 2 * 3 * #sizeof~INT;
axiom #sizeof~$Pointer$ > 0;
axiom #sizeof~BOOL > 0;
axiom #sizeof~REAL > 0;
procedure main() returns (#res : int);
    modifies #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool, ~mdga, ~mdgaHp.base, ~mdgaHp.offset;

procedure ULTIMATE.init() returns ();
    modifies #valid, #NULL.base, #NULL.offset, ~ga, ~pga.base, ~pga.offset, ~mdga, ~mdgaH.base, ~mdgaH.offset, ~mdgaHp.base, ~mdgaHp.offset, #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool;
    modifies #valid, #length, #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool;

procedure ULTIMATE.start() returns ();
    modifies #valid, #NULL.base, #NULL.offset, ~ga, ~pga.base, ~pga.offset, ~mdga, ~mdgaH.base, ~mdgaH.offset, ~mdgaHp.base, ~mdgaHp.offset, #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool, #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool, ~mdga, ~mdgaHp.base, ~mdgaHp.offset;
    modifies #memory_int, #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_real, #memory_bool, ~mdga, ~mdgaHp.base, ~mdgaHp.offset, #valid, #length;

