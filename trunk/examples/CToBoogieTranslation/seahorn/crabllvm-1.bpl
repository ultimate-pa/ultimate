implementation ULTIMATE.init() returns (){
  $Ultimate##0:
    #NULL.base, #NULL.offset := 0bv32, 0bv32;
    #valid := #valid[0bv32 := 0bv1];
    call ~#x.base, ~#x.offset := #Ultimate.alloc(4bv32);
    call write~INTTYPE4(5bv32, ~#x.base, ~#x.offset, 4bv32);
    ~y := 3bv32;
    ~a := ~a[0bv32 := 0bv32];
    ~a := ~a[1bv32 := 0bv32];
    ~a := ~a[2bv32 := 0bv32];
    ~a := ~a[3bv32 := 0bv32];
    ~a := ~a[4bv32 := 0bv32];
    ~a := ~a[5bv32 := 0bv32];
    ~a := ~a[6bv32 := 0bv32];
    ~a := ~a[7bv32 := 0bv32];
    ~a := ~a[8bv32 := 0bv32];
    ~a := ~a[9bv32 := 0bv32];
    return;
}

implementation ULTIMATE.start() returns (){
    var #t~ret6 : C_INT;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret6 := main();
    return;
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
    var #t~mem0 : C_INT;
    var #t~ret3 : C_INT;
    var #t~mem4 : C_INT;
    var #t~post2 : C_INT;
    var #t~post5 : C_INT;
    var ~i~2 : C_INT;
    var ~p~2.base : bv32, ~p~2.offset : bv32;
    var ~res~2 : C_INT;

  $Ultimate##0:
    havoc ~i~2;
    ~p~2.base, ~p~2.offset := ~#x.base, ~#x.offset;
    call #t~mem0 := read~INTTYPE4(~p~2.base, ~p~2.offset, 4bv32);
    call write~INTTYPE4(~bvadd32(#t~mem0, 1bv32), ~p~2.base, ~p~2.offset, 4bv32);
    havoc #t~mem0;
    ~i~2 := 0bv32;
    goto $Ultimate##1;
  $Ultimate##1:
    goto $Ultimate##2, $Ultimate##3;
  $Ultimate##2:
    assume true;
    goto $Ultimate##4, $Ultimate##5;
  $Ultimate##4:
    assume !~bvslt32(~i~2, 10bv32);
    goto $Ultimate##6;
  $Ultimate##5:
    assume !!~bvslt32(~i~2, 10bv32);
    call #t~ret3 := nd();
    goto $Ultimate##7, $Ultimate##8;
  $Ultimate##7:
    assume #t~ret3 != 0bv32;
    havoc #t~ret3;
    ~a := ~a[~i~2 := ~y];
    goto Loop~0;
  $Ultimate##8:
    assume !(#t~ret3 != 0bv32);
    havoc #t~ret3;
    call #t~mem4 := read~INTTYPE4(~#x.base, ~#x.offset, 4bv32);
    ~a := ~a[~i~2 := #t~mem4];
    havoc #t~mem4;
    goto Loop~0;
  Loop~0:
    #t~post2 := ~i~2;
    ~i~2 := ~bvadd32(#t~post2, 1bv32);
    havoc #t~post2;
    goto $Ultimate##1;
  $Ultimate##3:
    assume !true;
    goto $Ultimate##6;
  $Ultimate##6:
    #t~post5 := ~y;
    ~y := ~bvadd32(#t~post5, 1bv32);
    havoc #t~post5;
    ~res~2 := ~a[~bvsub32(~i~2, 1bv32)];
    assert ~bvsge32(~res~2, 0bv32) && ~bvsle32(~res~2, 6bv32);
    #res := ~res~2;
    return;
}

var ~#x.base : bv32, ~#x.offset : bv32;

var ~y : C_INT;

var ~a : [C_INT]C_INT;

var #NULL.base : bv32, #NULL.offset : bv32;

var #valid : [C_INT]bv1;

var #length : [C_INT]C_INT;

var #memory_INTTYPE4 : [bv32,bv32]bv32;

procedure write~INTTYPE4(#value : C_INT, #ptr.base : bv32, #ptr.offset : bv32, #sizeOfWrittenType : C_INT) returns ();
modifies #memory_INTTYPE4;
ensures true && #memory_INTTYPE4 == old(#memory_INTTYPE4)[#ptr.base,#ptr.offset := #value];

procedure read~INTTYPE4(#ptr.base : bv32, #ptr.offset : bv32, #sizeOfReadType : C_INT) returns (#value : C_INT);
ensures #value == #memory_INTTYPE4[#ptr.base,#ptr.offset];

procedure ULTIMATE.free(~addr.base : bv32, ~addr.offset : bv32) returns ();
free requires ~addr.offset == 0bv32;
free requires ~addr.base == 0bv32 || #valid[~addr.base] == 1bv1;
free ensures (if ~addr.base == 0bv32 then #valid == old(#valid) else #valid == old(#valid)[~addr.base := 0bv1]);
modifies #valid;

procedure ULTIMATE.dealloc(~addr.base : bv32, ~addr.offset : bv32) returns ();
free ensures #valid == old(#valid)[~addr.base := 0bv1];
modifies #valid;

procedure #Ultimate.alloc(~size : C_INT) returns (#res.base : bv32, #res.offset : bv32);
ensures old(#valid)[#res.base] == 0bv1;
ensures #valid == old(#valid)[#res.base := 1bv1];
ensures #res.offset == 0bv32;
ensures #res.base != 0bv32;
ensures #length == old(#length)[#res.base := ~size];
modifies #valid, #length;

procedure nd() returns (#res : C_INT);
modifies ;

procedure main() returns (#res : C_INT);
modifies #memory_INTTYPE4, ~a, ~y;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL.base, #NULL.offset, ~#x.base, ~#x.offset, ~y, ~a, #memory_INTTYPE4;
modifies #memory_INTTYPE4, #valid, #length;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL.base, #NULL.offset, ~#x.base, ~#x.offset, ~y, ~a, #memory_INTTYPE4, #memory_INTTYPE4, ~a, ~y;
modifies #memory_INTTYPE4, ~a, ~y, #valid, #length;

function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvslt" } ~bvslt32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsub" } ~bvsub32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvsge" } ~bvsge32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsle" } ~bvsle32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvadd" } ~bvadd8(in0 : C_CHAR, in1 : C_CHAR) returns (out : C_CHAR);
function { :builtin "bvadd" } ~bvadd16(in0 : C_SHORT, in1 : C_SHORT) returns (out : C_SHORT);
function { :builtin "bvadd" } ~bvadd64(in0 : C_LONG, in1 : C_LONG) returns (out : C_LONG);
