// without pointer structs
implementation f() returns (f : int){
    var #t~mem1 : int;

    #t~mem1 := #memoryPointer[p2];
    call writePointer(#t~mem1, p1, 4);
    havoc #t~mem1;
}

implementation main() returns (){
    var ret : int;
    var tmp7 : int;
    var tmp8, tmp : int;

    #memoryPointer[p2] := b;
    call ret := f();
    call write~int(ret, a, 4);
    memInt[b] := 8;
    #memoryPointer[b] := 7;
    tmp7 := #memoryPointer[p1];
    call tmp8 := read~int(tmp7, 4);
    assert (tmp8 == 8);
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
    call ULTIMATE.init();
    call main();
}

var memInt : [int]int;

procedure write~int(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies memInt, #memoryPointer;
ensures memInt == old(memInt)[#ptr := #value];
ensures #memoryPointer == old(#memoryPointer)[#ptr := #memoryPointer[#ptr]];


procedure read~int(#ptr : int, #sizeOfReadType : int) returns (#value : int);
ensures #value == memInt[#ptr];


var #memoryPointer : [int]int;

procedure writePointer(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies memInt, #memoryPointer;
ensures #memoryPointer == old(#memoryPointer)[#ptr := #value];


procedure f() returns (f : int);
modifies #memoryPointer, memInt;

procedure main() returns ();
modifies #memoryPointer, memInt;

procedure ULTIMATE.init() returns ();
modifies a, b, p1, p2, memInt, #memoryPointer;
modifies memInt, #memoryPointer;

procedure ULTIMATE.start() returns ();
modifies a, b, p1, p2, memInt, #memoryPointer, #memoryPointer, memInt;

modifies #memoryPointer, memInt;

