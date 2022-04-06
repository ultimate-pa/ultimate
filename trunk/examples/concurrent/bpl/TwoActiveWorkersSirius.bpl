//#Safe
/*
 * Although, the system can construct infinitely many
 * threads there are only two active threads at each
 * point in time.
 * (Sirius is a binary star system consisting of two stars.)
 * Author: Dominik, Frank, Matthias
 * Date: 2022-01-11
 * 
 */

var ctr : int;
var i : int;

procedure ULTIMATE.start()
modifies ctr, i;
{
    ctr := 0;
    i := 0;
    while (*) {
        fork i worker();
        if (i > 0) { join i-1; }
        i := i + 1;
    }
}

procedure worker()
modifies ctr;
{
    ctr := ctr + i;
    assert ctr <= 2 * i;
    ctr := ctr - i;
}

