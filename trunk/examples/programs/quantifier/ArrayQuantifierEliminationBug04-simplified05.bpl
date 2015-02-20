// without pointer structs
implementation f() returns (f : int){
    var #t~mem1 : int;

    call #t~mem1 := readPointer(p2, 4);
    call writePointer(#t~mem1, p1, 4);
    havoc #t~mem1;
}

implementation main() returns (main : int){
    var ret : int;
    var tmp7 : int;
    var tmp8 : int;

    call writePointer(b, p2, 4);
    call ret := f();
    call write~int(ret, a, 4);
    call write~int(8, b, 4);
//    call tmp7 := readPointer(p1, 4);
	tmp7 := memPtr[p1];
    call tmp8 := read~int(tmp7, 4);
// 	tmp8 := memInt[tmp7];
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
    var #t~ret9 : int;

    call ULTIMATE.init();
    call #t~ret9 := main();
}

var #NULL : int;

var memInt : [int]int;

procedure write~int(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies memInt, memPtr;
ensures memInt == old(memInt)[#ptr := #value];
ensures memPtr == old(memPtr)[#ptr := memPtr[#ptr]];


procedure read~int(#ptr : int, #sizeOfReadType : int) returns (#value : int);
ensures #value == memInt[#ptr];


var memPtr : [int]int;

procedure writePointer(#value : int, #ptr : int, #sizeOfWrittenType : int) returns ();
modifies memInt, memPtr;
ensures memPtr == old(memPtr)[#ptr := #value];
procedure readPointer(#ptr : int, #sizeOfReadType : int) returns (#value : int);
ensures #value == memPtr[#ptr];



procedure f() returns (f : int);
modifies memPtr, memInt;

procedure main() returns (main : int);
modifies memPtr, memInt;

procedure ULTIMATE.init() returns ();
modifies a, b, p1, p2, memInt, memPtr;
modifies memInt, memPtr;

procedure ULTIMATE.start() returns ();
modifies a, b, p1, p2, memInt, memPtr, memPtr, memInt;

modifies memPtr, memInt;

