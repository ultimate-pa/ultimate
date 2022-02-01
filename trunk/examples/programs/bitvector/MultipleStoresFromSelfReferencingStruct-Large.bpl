//#Safe
/* Date: 2017-10-08
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Example where we need "multiple stores" in our partial quantifier
 * elimination for arrays.
 * 
 */

implementation ULTIMATE.init() returns (){
    #NULL := { base: 0bv32, offset: 0bv32 };
    #valid[0bv32] := 0bv1;
}

implementation ULTIMATE.start() returns (){
    var #t~ret3 : C_INT;

    call ULTIMATE.init();
    call #t~ret3 := main();
}

type { :isUnsigned false } { :bitsize 8 } C_CHAR = bv8;
type { :isUnsigned false } { :bitsize 8 } C_SCHAR = bv8;
type { :isUnsigned true } { :bitsize 8 } C_UCHAR = bv8;
type { :isUnsigned false } { :bitsize 16 } C_SHORT = bv16;
type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
type { :isUnsigned false } { :bitsize 32 } C_INT = bv32;
type { :isUnsigned true } { :bitsize 32 } C_UINT = bv32;
type { :isUnsigned false } { :bitsize 64 } C_LONG = bv64;
type { :isUnsigned true } { :bitsize 64 } C_ULONG = bv64;
type { :isUnsigned false } { :bitsize 64 } C_LONGLONG = bv64;
type { :isUnsigned true } { :bitsize 64 } C_ULONGLONG = bv64;
type { :isUnsigned true } { :bitsize 8 } C_BOOL = bv8;
implementation main() returns (#res : C_INT){
    var #t~malloc0 : $Pointer$;
    var #t~mem2 : C_INT;
    var ~p~1 : $Pointer$;
//     var ~a~1 : C_INT;

    call #t~malloc0 := #Ultimate.alloc(20bv32);
    ~p~1 := #t~malloc0;
    call write~intINTTYPE4(3bv32, { base: ~p~1!base, offset: ~bvadd32(~p~1!offset, 0bv32) }, 4bv32);
    call #t~mem2 := read~intINTTYPE4({ base: ~p~1!base, offset: ~bvadd32(~p~1!offset, 0bv32) }, 4bv32);
//     ~a~1 := #t~mem2;
//     havoc #t~mem2;
    assert #t~mem2 == 3bv32;
//     call ULTIMATE.free(~p~1);
}

var #NULL : $Pointer$;

var #valid : [C_INT]bv1;

var #length : [C_INT]C_INT;

var #memory_int : [$Pointer$]bv16;

procedure write~intINTTYPE4(#value : C_INT, #ptr : $Pointer$, #sizeOfWrittenType : C_INT) returns ();
// requires #valid[#ptr!base] == 1bv1;
// requires ~bvsle32(~bvadd32(#sizeOfWrittenType, #ptr!offset), #length[#ptr!base]) && ~bvsle32(0bv32, #ptr!offset);
modifies #memory_int;
ensures (true && #memory_int == old(#memory_int)[#ptr := #value[16:0]]) && #memory_int == old(#memory_int)[{ base: #ptr!base, offset: ~bvadd32(#ptr!offset, 2bv32) } := #value[32:16]];

procedure read~intINTTYPE4(#ptr : $Pointer$, #sizeOfReadType : C_INT) returns (#value : C_INT);
requires #valid[#ptr!base] == 1bv1;
// requires ~bvsle32(~bvadd32(#sizeOfReadType, #ptr!offset), #length[#ptr!base]) && ~bvsle32(0bv32, #ptr!offset);
ensures #value == #memory_int[{ base: #ptr!base, offset: ~bvadd32(#ptr!offset, 2bv32) }] ++ #memory_int[#ptr];





procedure #Ultimate.alloc(~size : C_INT) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == 0bv1;
ensures #valid == old(#valid)[#res!base := 1bv1];
ensures #res!offset == 0bv32;
ensures #res!base != 0bv32;
ensures #length == old(#length)[#res!base := ~size];
modifies #valid, #length;

type $Pointer$ = { base : C_INT, offset : C_INT };
procedure main() returns (#res : C_INT);
modifies #memory_int, #valid, #length;
ensures #valid == old(#valid);

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL;
modifies ;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, #memory_int;
modifies #valid, #length, #memory_int;

function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvadd" } ~bvadd8(in0 : C_CHAR, in1 : C_CHAR) returns (out : C_CHAR);
function { :builtin "bvadd" } ~bvadd16(in0 : C_SHORT, in1 : C_SHORT) returns (out : C_SHORT);
function { :builtin "bvadd" } ~bvadd64(in0 : C_LONG, in1 : C_LONG) returns (out : C_LONG);
function { :builtin "bvsle" } ~bvsle32(in0 : C_INT, in1 : C_INT) returns (out : bool);
