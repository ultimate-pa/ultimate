//#Safe

var A : int;
var B : int;
var C : int;
var D : int;


procedure ULTIMATE.init() returns ()
modifies B, A, D, C;
{
    A := 0;
    B := 0;
    C := 7;
    D := 0;
}

procedure ULTIMATE.start() returns ()
modifies B, A, D, C;
{
    var #t~ret2 : int;

    call ULTIMATE.init();
    call #t~ret2 := main();
}

procedure foo(in1 : int) returns (#res : int)
modifies B, A, D, C;
{
    var i : int;

    i := in1;
    if (false) {
    } else if (i != 0) {
        B := 1;
        #res := 0;
        return;
    }
    if (C == 7 && A == 0) {
        if (false) {
            A := 0;
            D := 0;
            C := 0;
        }
    }
    if (A != 0 && B == 0) {
        assert false;
    }
}

procedure main() returns (#res : int)
modifies B, A, D, C;
{
    var #t~nondet0 : int;
    var #t~ret1 : int;
    var i : int;

    while (true)
    {
        if (false) {
            break;
        }
        havoc i;
        assume -2147483648 <= #t~nondet0 && #t~nondet0 <= 2147483647;
        i := #t~nondet0;
        havoc #t~nondet0;
        if (i != 0 && i != 1) {
            #res := 0;
            return;
        }
        call #t~ret1 := foo(i);

    }
}
