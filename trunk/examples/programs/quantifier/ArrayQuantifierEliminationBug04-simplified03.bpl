// without pointer structs
implementation f() returns (f : int){
    var #t~mem1 : int;

    call #t~mem1 := readPointer(~pp2~1, 4);
    call writePointer(#t~mem1, ~pp1~1, 4);
    havoc #t~mem1;
}

implementation main() returns (main : int){
    var #t~ret4 : int;
    var #t~mem7 : int;
    var #t~mem8 : int;
    var ~px~3 : int;

    call writePointer(~#b~1, ~#p2~1, 4);
    ~pp1~1 := ~#p1~1;
    ~pp2~1 := ~#p2~1;
    call #t~ret4 := f();
    call write~int(#t~ret4, ~#a~1, 4);
    call write~int(8, ~#b~1, 4);
    call #t~mem7 := readPointer(~#p1~1, 4);
    call #t~mem8 := read~int(#t~mem7, 4);
    assert (#t~mem8 == 8);
    return;
}

var ~#a~1 : int;

var ~#b~1 : int;

var ~#p1~1 : int;

var ~#p2~1 : int;

var ~pp1~1 : int;

var ~pp2~1 : int;

implementation ULTIMATE.init() returns (){
    call ~#a~1 := ~malloc(4);
    call ~#b~1 := ~malloc(4);
    call write~int(0, ~#b~1, 4);
    call ~#p1~1 := ~malloc(4);
    call writePointer(#NULL, ~#p1~1, 4);
    call writePointer(#NULL, ~#p2~1, 4);
}

implementation ULTIMATE.start() returns (){
    var #t~ret9 : int;

    call ULTIMATE.init();
    call #t~ret9 := main();
}

var #NULL : int;

var #memory_int : [int]int;

procedure write~int(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies #memory_int, #memoryPointer;
ensures #memory_int == old(#memory_int)[#ptr := #value];
ensures #memoryPointer == old(#memoryPointer)[#ptr := #memoryPointer[#ptr]];


procedure read~int(#ptr : int, #sizeOfReadType : int) returns (#value : int);
ensures #value == #memory_int[#ptr];


var #memoryPointer : [int]int;

procedure writePointer(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies #memory_int, #memoryPointer;
ensures #memoryPointer == old(#memoryPointer)[#ptr := #value];
procedure readPointer(#ptr : int, #sizeOfReadType : int) returns (#value : int);
ensures #value == #memoryPointer[#ptr];

var #valid : [int]bool;
var #length : [int]int;

procedure ~malloc(~size : int) returns (#res : int);
ensures old(#valid)[#res] == false;
ensures #valid == old(#valid)[#res := true];
modifies #valid;


procedure f() returns (f : int);
modifies #memoryPointer, #memory_int;

procedure main() returns (main : int);
modifies #memoryPointer, ~pp1~1, ~pp2~1, #memory_int;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL, ~#a~1, ~#b~1, ~#p1~1, ~#p2~1, ~pp1~1, ~pp2~1, #memory_int, #memoryPointer;
modifies #valid, #memory_int, #memoryPointer;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, ~#a~1, ~#b~1, ~#p1~1, ~#p2~1, ~pp1~1, ~pp2~1, #memory_int, #memoryPointer, #memoryPointer, ~pp1~1, ~pp2~1, #memory_int;

modifies #memoryPointer, ~pp1~1, ~pp2~1, #memory_int, #valid;

