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

procedure calculate_output(#in~input : int) returns (#res : int)
modifies B, A, D, C;
{
    var ~input : int;

    ~input := #in~input;
    if (false) {
    } else if (~input != 0) {
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
    var ~input~7 : int;

    while (true)
    {
        if (false) {
            break;
        }
        havoc ~input~7;
        assume -2147483648 <= #t~nondet0 && #t~nondet0 <= 2147483647;
        ~input~7 := #t~nondet0;
        havoc #t~nondet0;
        if (~input~7 != 0 && ~input~7 != 1) {
            #res := 0;
            return;
        }
        call #t~ret1 := calculate_output(~input~7);

    }
}
