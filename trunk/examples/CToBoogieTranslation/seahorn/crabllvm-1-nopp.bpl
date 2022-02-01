implementation ULTIMATE.init() returns (){
    #NULL := { base: 0bv32, offset: 0bv32 };
    #valid[0bv32] := 0bv1;
    call ~#x := #Ultimate.alloc(4bv32);
    call write~INTTYPE4(5bv32, ~#x, 4bv32);
    ~y := 3bv32;
    ~a[0bv32] := 0bv32;
    ~a[1bv32] := 0bv32;
    ~a[2bv32] := 0bv32;
    ~a[3bv32] := 0bv32;
    ~a[4bv32] := 0bv32;
    ~a[5bv32] := 0bv32;
    ~a[6bv32] := 0bv32;
    ~a[7bv32] := 0bv32;
    ~a[8bv32] := 0bv32;
    ~a[9bv32] := 0bv32;
}

implementation ULTIMATE.start() returns (){
    var #t~ret6 : C_INT;

    call ULTIMATE.init();
    call #t~ret6 := main();
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
    var ~p~2 : $Pointer$;
    var ~res~2 : C_INT;

    havoc ~i~2;
    ~p~2 := ~#x;
    call #t~mem0 := read~INTTYPE4(~p~2, 4bv32);
    call write~INTTYPE4(~bvadd32(#t~mem0, 1bv32), ~p~2, 4bv32);
    havoc #t~mem0;
    ~i~2 := 0bv32;
    while (true)
    {
        if (!~bvslt32(~i~2, 10bv32)) {
            break;
        }
        call #t~ret3 := nd();
        if (#t~ret3 != 0bv32) {
            havoc #t~ret3;
            ~a[~i~2] := ~y;
        } else {
            havoc #t~ret3;
            call #t~mem4 := read~INTTYPE4(~#x, 4bv32);
            ~a[~i~2] := #t~mem4;
            havoc #t~mem4;
        }
      Loop~0:
        #t~post2 := ~i~2;
        ~i~2 := ~bvadd32(#t~post2, 1bv32);
        havoc #t~post2;
    }
    #t~post5 := ~y;
    ~y := ~bvadd32(#t~post5, 1bv32);
    havoc #t~post5;
    ~res~2 := ~a[~bvsub32(~i~2, 1bv32)];
    assert ~bvsge32(~res~2, 0bv32) && ~bvsle32(~res~2, 6bv32);
    #res := ~res~2;
    return;
}

var ~#x : $Pointer$;

var ~y : C_INT;

var ~a : [C_INT]C_INT;

var #NULL : $Pointer$;

var #valid : [C_INT]bv1;

var #length : [C_INT]C_INT;

var #memory_INTTYPE4 : [$Pointer$]C_INT;

procedure write~INTTYPE4(#value : C_INT, #ptr : $Pointer$, #sizeOfWrittenType : C_INT) returns ();
modifies #memory_INTTYPE4;
ensures true && #memory_INTTYPE4 == old(#memory_INTTYPE4)[#ptr := #value];

procedure read~INTTYPE4(#ptr : $Pointer$, #sizeOfReadType : C_INT) returns (#value : C_INT);
ensures #value == #memory_INTTYPE4[#ptr];

procedure ULTIMATE.free(~addr : $Pointer$) returns ();
free requires ~addr!offset == 0bv32;
free requires ~addr!base == 0bv32 || #valid[~addr!base] == 1bv1;
free ensures (if ~addr!base == 0bv32 then #valid == old(#valid) else #valid == old(#valid)[~addr!base := 0bv1]);
modifies #valid;

procedure ULTIMATE.dealloc(~addr : $Pointer$) returns ();
free ensures #valid == old(#valid)[~addr!base := 0bv1];
modifies #valid;

procedure #Ultimate.alloc(~size : C_INT) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == 0bv1;
ensures #valid == old(#valid)[#res!base := 1bv1];
ensures #res!offset == 0bv32;
ensures #res!base != 0bv32;
ensures #length == old(#length)[#res!base := ~size];
modifies #valid, #length;

type $Pointer$ = { base : C_INT, offset : C_INT };
procedure nd() returns (#res : C_INT);
modifies ;

procedure main() returns (#res : C_INT);
modifies #memory_INTTYPE4, ~a, ~y;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL, ~#x, ~y, ~a, #memory_INTTYPE4;
modifies #memory_INTTYPE4, #valid, #length;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, ~#x, ~y, ~a, #memory_INTTYPE4, #memory_INTTYPE4, ~a, ~y;
modifies #memory_INTTYPE4, ~a, ~y, #valid, #length;

function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvslt" } ~bvslt32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsub" } ~bvsub32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvsge" } ~bvsge32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsle" } ~bvsle32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvadd" } ~bvadd8(in0 : C_CHAR, in1 : C_CHAR) returns (out : C_CHAR);
function { :builtin "bvadd" } ~bvadd16(in0 : C_SHORT, in1 : C_SHORT) returns (out : C_SHORT);
function { :builtin "bvadd" } ~bvadd64(in0 : C_LONG, in1 : C_LONG) returns (out : C_LONG);
