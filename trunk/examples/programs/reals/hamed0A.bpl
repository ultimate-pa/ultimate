// Program obtained from Hamad Ladan's plugin which transforms PEAs into Boogie programs. 
var bndResG0_X2, bndResG1_X2, minDurG2_X2, maxDurG3_X1 : real, pc0, pc1, pc2, pc3, pc4 : int, delta : real, V0, V0', V1, V1', V2, V2' : bool;
procedure myProcedure() returns ()
    modifies bndResG0_X2, bndResG1_X2, minDurG2_X2, maxDurG3_X1, pc0, pc1, pc2, pc3, pc4, delta, V0, V0', V1, V1', V2, V2';
{
    havoc pc0, pc1, pc2, pc3, pc4;
    assume (((pc0 == 0 && (pc1 == 0 || pc1 == 2)) && (pc2 == 0 || pc2 == 2)) && (pc3 == 0 || pc3 == 1)) && (pc4 == 0 || pc4 == 1);
    havoc bndResG0_X2, bndResG1_X2, minDurG2_X2, maxDurG3_X1;
    assume ((bndResG0_X2 == 0.0 && bndResG1_X2 == 0.0) && minDurG2_X2 == 0.0) && maxDurG3_X1 == 0.0;
    while (*)
    {
        havoc V0', V1', V2', delta;
        assume delta > 0.0;
        bndResG0_X2 := bndResG0_X2 + delta;
        bndResG1_X2 := bndResG1_X2 + delta;
        minDurG2_X2 := minDurG2_X2 + delta;
        maxDurG3_X1 := maxDurG3_X1 + delta;
        if (pc0 == 0) {
            assume true;
            assume !V0 || !V1;
        }
        if (pc1 == 2) {
            assume bndResG0_X2 <= 10.0;
            assume !V0 && V2;
        } else if (pc1 == 1) {
            assume bndResG0_X2 <= 10.0;
            assume !V0 && !V2;
        } else if (pc1 == 0) {
            assume true;
            assume !V2 || V0;
        }
        if (pc2 == 2) {
            assume bndResG1_X2 <= 8.0;
            assume !V1 && V2;
        } else if (pc2 == 1) {
            assume bndResG1_X2 <= 8.0;
            assume !V1 && !V2;
        } else if (pc2 == 0) {
            assume true;
            assume !V2 || V1;
        }
        if (pc3 == 2) {
            assume minDurG2_X2 <= 15.0;
            assume !V2;
        } else if (pc3 == 1) {
            assume true;
            assume V2;
        } else if (pc3 == 0) {
            assume true;
            assume !V2;
        }
        if (pc4 == 1) {
            assume maxDurG3_X1 < 1.0;
            assume V2;
        } else if (pc4 == 0) {
            assume true;
            assume !V2;
        }
        assert (pc0 == 0 && pc1 == 2 && pc2 == 2 ==> bndResG1_X2 < 8.0 || bndResG0_X2 < 10.0) && (pc0 == 0 && pc1 == 2 && pc2 == 1 ==> bndResG1_X2 < 8.0 || bndResG0_X2 < 10.0) && (pc0 == 0 && pc1 == 1 && pc2 == 2 ==> bndResG1_X2 < 8.0 || bndResG0_X2 < 10.0) && (pc0 == 0 && pc1 == 1 && pc2 == 1 ==> bndResG1_X2 < 8.0 || bndResG0_X2 < 10.0);
        if (pc0 == 0) {
            if (*) {
                assume true;
                pc0 := 0;
            } else {
                assume false;
            }
        }
        if (pc1 == 2) {
            if (*) {
                assume bndResG0_X2 < 10.0;
                pc1 := 2;
            } else if (*) {
                assume bndResG0_X2 < 10.0;
                pc1 := 1;
            } else if (*) {
                assume V0';
                pc1 := 0;
            } else {
                assume false;
            }
        } else if (pc1 == 1) {
            if (*) {
                assume bndResG0_X2 < 10.0;
                pc1 := 2;
            } else if (*) {
                assume bndResG0_X2 < 10.0;
                pc1 := 1;
            } else if (*) {
                assume V0';
                pc1 := 0;
            } else {
                assume false;
            }
        } else if (pc1 == 0) {
            if (*) {
                assume true;
                bndResG0_X2 := 0.0;
                pc1 := 2;
            } else if (*) {
                assume true;
                pc1 := 0;
            } else {
                assume false;
            }
        }
        if (pc2 == 2) {
            if (*) {
                assume bndResG1_X2 < 8.0;
                pc2 := 2;
            } else if (*) {
                assume bndResG1_X2 < 8.0;
                pc2 := 1;
            } else if (*) {
                assume V1';
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 1) {
            if (*) {
                assume bndResG1_X2 < 8.0;
                pc2 := 2;
            } else if (*) {
                assume bndResG1_X2 < 8.0;
                pc2 := 1;
            } else if (*) {
                assume V1';
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 0) {
            if (*) {
                assume true;
                bndResG1_X2 := 0.0;
                pc2 := 2;
            } else if (*) {
                assume true;
                pc2 := 0;
            } else {
                assume false;
            }
        }
        if (pc3 == 2) {
            if (*) {
                assume minDurG2_X2 >= 15.0 || !V2';
                pc3 := 1;
            } else if (*) {
                assume minDurG2_X2 < 15.0;
                pc3 := 2;
            } else if (*) {
                assume minDurG2_X2 >= 15.0;
                pc3 := 0;
            } else {
                assume false;
            }
        } else if (pc3 == 1) {
            if (*) {
                assume true;
                pc3 := 1;
            } else if (*) {
                assume true;
                minDurG2_X2 := 0.0;
                pc3 := 2;
            } else {
                assume false;
            }
        } else if (pc3 == 0) {
            if (*) {
                assume true;
                pc3 := 1;
            } else if (*) {
                assume true;
                pc3 := 0;
            } else {
                assume false;
            }
        }
        if (pc4 == 1) {
            if (*) {
                assume true;
                pc4 := 1;
            } else if (*) {
                assume true;
                pc4 := 0;
            } else {
                assume false;
            }
        } else if (pc4 == 0) {
            if (*) {
                assume true;
                maxDurG3_X1 := 0.0;
                pc4 := 1;
            } else if (*) {
                assume true;
                pc4 := 0;
            } else {
                assume false;
            }
        }
        V0 := V0';
        V1 := V1';
        V2 := V2';
    }
}

