//#Safe
implementation nonMain(#in~p.base:int, #in~p.offset:int, #in~q.base:int, #in~q.offset:int) returns (#res:int)
{
    var ~p.base : int, ~p.offset : int;
    var ~q.base : int, ~q.offset : int;
    var #t~mem0 : int;
    var #t~mem1 : int;
    var #t~mem2 : int;

  UltimateLabel0:
    ~p.base, ~p.offset := #in~p.base, #in~p.offset;
    ~q.base, ~q.offset := #in~q.base, #in~q.offset;
    call write~int(23, ~p.base, ~p.offset);
    havoc #t~mem0;
    call write~int(42, ~q.base, ~q.offset);
    havoc #t~mem1;
    call #t~mem2 := read~int(~p.base, ~p.offset);
  UltimateLabel1:
    assume 42 == #t~mem2;
    havoc #t~mem2;
    assert ~q.base == ~p.base && ~q.offset == ~p.offset;
    goto UltimateLabel3;
  UltimateLabel3:
    return;
}

var #NULL.base : int, #NULL.offset : int;
var #memory_$Pointer$.base : [int,int]int, #memory_$Pointer$.offset : [int,int]int;

var #memory_int : [int,int]int;
procedure write~int(#value:int, #ptr.base:int, #ptr.offset:int) returns ();
    modifies #memory_real, #memory_bool, #memory_$Pointer$.offset, #memory_$Pointer$.base, #memory_int;
    ensures old(#memory_$Pointer$.base)[#ptr.base,#ptr.offset := #memory_$Pointer$.base[#ptr.base,#ptr.offset]] == #memory_$Pointer$.base && old(#memory_$Pointer$.offset)[#ptr.base,#ptr.offset := #memory_$Pointer$.offset[#ptr.base,#ptr.offset]] == #memory_$Pointer$.offset;
    ensures old(#memory_int)[#ptr.base,#ptr.offset := #value] == #memory_int;
    ensures old(#memory_bool)[#ptr.base,#ptr.offset := #memory_bool[#ptr.base,#ptr.offset]] == #memory_bool;
    ensures old(#memory_real)[#ptr.base,#ptr.offset := #memory_real[#ptr.base,#ptr.offset]] == #memory_real;

procedure read~int(#ptr.base:int, #ptr.offset:int) returns (#value:int);
    ensures #memory_int[#ptr.base,#ptr.offset] == #value;

var #memory_bool : [int,int]bool;


var #memory_real : [int,int]real;


var #valid : [int]bool;
var #length : [int]int;


const #sizeof~real : int;
const #sizeof~bool : int;
const #sizeof~int : int;
const #sizeof~$Pointer$ : int;
axiom #sizeof~bool > 0;
axiom #sizeof~$Pointer$ > 0;
axiom #sizeof~real > 0;
axiom #sizeof~int > 0;
procedure nonMain(#in~p.base:int, #in~p.offset:int, #in~q.base:int, #in~q.offset:int) returns (#res:int);
    modifies #memory_real, #memory_bool, #memory_$Pointer$.offset, #memory_$Pointer$.base, #memory_int;

procedure ULTIMATE.init() returns ();
    modifies #NULL.offset, #valid, #NULL.base;

implementation ULTIMATE.init() returns ()
{
  UltimateLabel0:
    #valid := #valid[0 := false];
    #NULL.base := 0;
    return;
}

