// sd


implementation main() returns (){
    var ii : int;
    var offset : int;
    var base : int;

    mem[i] := i;
    assume i <= len[base];
    ii := mem[i];
    assert ii == i;
    i := ii - 10;
    assert i <= len[base];
}

implementation ULTIMATE.start() returns (){
    call main();
}

var mem : [int]int;
var len : [int]int;
var i : int;

procedure main() returns ();
modifies mem, len, i;

procedure ULTIMATE.start() returns ();
modifies len, mem, i;

