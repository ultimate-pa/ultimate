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

var c, i : int;

procedure ULTIMATE.start()
modifies c, i;
{
    c := 0;
    i := 0;
    while (true) {
        fork i worker();
        if (i > 0) { join i-1; }
        i := i + 1;
    }
}

procedure worker()
modifies c;
{
    c := c + i;
    assert c <= 2 * i;
    c := c - i;
}

