// without pointer structs
implementation f() returns (f : int){
    var #t~mem1 : int;

    call #t~mem1 := readPointer(p2, 4);
    call writePointer(#t~mem1, p1, 4);
    havoc #t~mem1;
}

implementation main() returns (main : int){
    var #t~ret4 : int;
    var #t~mem7 : int;
    var #t~mem8 : int;

    call writePointer(b, p2, 4);
    call #t~ret4 := f();
    call write~int(#t~ret4, a, 4);
    call write~int(8, b, 4);
    call #t~mem7 := readPointer(p1, 4);
    call #t~mem8 := read~int(#t~mem7, 4);
    assert (#t~mem8 == 8);
    return;
}

var a : int;
var b : int;
var p1 : int;
var p2 : int;


implementation ULTIMATE.init() returns (){
    assume a != p1;
    assume b != p1;
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



procedure f() returns (f : int);
modifies #memoryPointer, #memory_int;

procedure main() returns (main : int);
modifies #memoryPointer, #memory_int;

procedure ULTIMATE.init() returns ();
modifies a, b, p1, p2, #memory_int, #memoryPointer;
modifies #memory_int, #memoryPointer;

procedure ULTIMATE.start() returns ();
modifies a, b, p1, p2, #memory_int, #memoryPointer, #memoryPointer, #memory_int;

modifies #memoryPointer, #memory_int;

