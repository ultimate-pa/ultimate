//#Unsafe
var g : int;
var nondet : int;
implementation callee(b:int) returns (res:int)
{
    if (nondet != 0) {
        res := b + 1;
    } else {
        call delay();
        res := b;
    }
    return;
}

implementation main() returns (#res:int)
{
    var x : int;
    var a : int;

    call a := callee(x);
    assert a == x + 1;
}


procedure delay() returns ();
    modifies ;

procedure callee(b:int) returns (#res:int);
    modifies ;

procedure main() returns (#res:int);
    modifies ;


