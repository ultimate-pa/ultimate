// Program obtained from Hamad Ladan's plugin which transforms PEAs into Boogie programs. 
var c1, c2 : real, pc0, pc1 : int, delta : real, A, A', B, B' : bool, b, a, c : bool;
procedure myProcedure() returns ()
    modifies c1, c2, pc0, pc1, delta, A, A', B, B', b, a, c;
{
    havoc pc0, pc1;
    assume pc0 == 1 && pc1 == 1;
    havoc c1, c2;
    assume c1 == 0.0 && c2 == 0.0;
    while (*)
    {
        havoc A', B', b, a, c, delta;
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
            assume !B;
        } else if (pc1 == 0) {
            assume c2 <= 5.0;
            assume B;
        }
        assert (pc0 == 1 && pc1 == 1 ==> c1 <= 2.0) && (pc0 == 1 && pc1 == 0 ==> c1 <= 2.0 && c2 < 5.0) && (pc0 == 0 && pc1 == 1 ==> c1 < 2.0) && (pc0 == 0 && pc1 == 0 ==> c1 <= 2.0);
        if (pc0 == 1) {
            if (*) {
                assume a && !b && c1 <= 2.0;
                c1 := 0.0;
                pc0 := 0;
            } else if (*) {
                assume !a && !b && c1 < 2.0;
                pc0 := 1;
            } else {
                assume false;
            }
        } else if (pc0 == 0) {
            if (*) {
                assume !a && b && c1 <= 2.0;
                c1 := 0.0;
                pc0 := 1;
            } else if (*) {
                assume !a && !b && c1 < 2.0;
                pc0 := 0;
            } else {
                assume false;
            }
        }
        if (pc1 == 1) {
            if (*) {
                assume !b && c;
                c2 := 0.0;
                pc1 := 0;
            } else if (*) {
                assume !b && !c;
                pc1 := 1;
            } else {
                assume false;
            }
        } else if (pc1 == 0) {
            if (*) {
                assume b && !c;
                c2 := 0.0;
                pc1 := 1;
            } else if (*) {
                assume !b && !c && c2 < 5.0;
                pc1 := 0;
            } else {
                assume false;
            }
        }
        A := A';
        B := B';
    }
}

