// Program obtained from Hamad Ladan's plugin which transforms PEAs into Boogie programs. 
var c1, c2 : real, pc0, pc1 : int, delta : real, A, A', B, B' : bool;
procedure myProcedure() returns ()
    modifies c1, c2, pc0, pc1, delta, A, A', B, B';
{
    havoc pc0, pc1;
    assume pc0 == 1 && pc1 == 1;
    havoc c1, c2;
    assume c1 == 0.0 && c2 == 0.0;
    while (*)
    {
        havoc A', B', delta;
        assume delta > 0.0;
        c1 := c1 + delta;
        c2 := c2 + delta;
        if (pc0 == 1) {
            assume c1 <= 2.0;
            assume !B || A;
        } else if (pc0 == 0) {
            assume c1 <= 2.0;
            assume !A && B;
        }
        if (pc1 == 1) {
            assume true;
            assume !A;
        } else if (pc1 == 0) {
            assume c2 <= 5.0;
            assume B;
        }
        assert (pc0 == 1 && pc1 == 1 ==> c1 < 2.0) && (pc0 == 1 && pc1 == 0 ==> c1 < 2.0 && c2 < 5.0) && (pc0 == 0 && pc1 == 1 ==> c1 < 2.0) && (pc0 == 0 && pc1 == 0 ==> c1 < 2.0 && c2 < 5.0);
        if (pc0 == 1) {
            if (*) {
                assume c1 < 2.0 && B';
                c1 := 0.0;
                pc0 := 0;
            } else if (*) {
                assume c1 < 2.0;
                pc0 := 1;
            } else {
                assume false;
            }
        } else if (pc0 == 0) {
            if (*) {
                assume c1 < 2.0 && A';
                pc0 := 1;
            } else if (*) {
                assume c1 < 2.0;
                pc0 := 0;
            } else {
                assume false;
            }
        }
        if (pc1 == 1) {
            if (*) {
                assume true;
                c2 := 0.0;
                pc1 := 0;
            } else if (*) {
                assume true;
                pc1 := 1;
            } else {
                assume false;
            }
        } else if (pc1 == 0) {
            if (*) {
                assume c2 < 5.0 && !B';
                pc1 := 1;
            } else if (*) {
                assume c2 < 5.0;
                pc1 := 0;
            } else {
                assume false;
            }
        }
        A := A';
        B := B';
    }
}

