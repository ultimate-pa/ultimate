// Program obtained from Hamad Ladan's plugin which transforms PEAs into Boogie programs. 
var bndResG0_X2, bndResG1_X2, minDurG2_X2, minDurG3_X2 : real, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7 : int, delta : real, V0, V0', V1, V1', V2, V2', V3, V3', V4, V4', V5, V5', V6, V6' : bool;
procedure myProcedure() returns ()
    modifies bndResG0_X2, bndResG1_X2, minDurG2_X2, minDurG3_X2, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, delta, V0, V0', V1, V1', V2, V2', V3, V3', V4, V4', V5, V5', V6, V6';
{
    havoc pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7;
    assume ((((((pc0 == 0 && (pc1 == 0 || pc1 == 2)) && (pc2 == 0 || pc2 == 2)) && (pc3 == 0 || pc3 == 1)) && ((pc4 == 0 || pc4 == 2) || pc4 == 6)) && (pc5 == 0 || pc5 == 2)) && pc6 == 0) && (pc7 == 0 || pc7 == 1);
    havoc bndResG0_X2, bndResG1_X2, minDurG2_X2, minDurG3_X2;
    assume ((bndResG0_X2 == 0.0 && bndResG1_X2 == 0.0) && minDurG2_X2 == 0.0) && minDurG3_X2 == 0.0;
    while (*)
    {
        havoc V0', V1', V2', V3', V4', V5', V6', delta;
        assume delta > 0.0;
        bndResG0_X2 := bndResG0_X2 + delta;
        bndResG1_X2 := bndResG1_X2 + delta;
        minDurG2_X2 := minDurG2_X2 + delta;
        minDurG3_X2 := minDurG3_X2 + delta;
        if (pc0 == 0) {
            assume true;
            assume !V0;
        }
        if (pc1 == 2) {
            assume bndResG0_X2 <= 10.0;
            assume V0 && !V1;
        } else if (pc1 == 1) {
            assume bndResG0_X2 <= 10.0;
            assume !V0 && !V1;
        } else if (pc1 == 0) {
            assume true;
            assume !V0 || V1;
        }
        if (pc2 == 2) {
            assume bndResG1_X2 <= 10.0;
            assume V2 && V3;
        } else if (pc2 == 1) {
            assume bndResG1_X2 <= 10.0;
            assume !V2 && V3;
        } else if (pc2 == 0) {
            assume true;
            assume !V2 || !V3;
        }
        if (pc3 == 2) {
            assume minDurG2_X2 <= 15.0;
            assume V3;
        } else if (pc3 == 1) {
            assume true;
            assume !V3;
        } else if (pc3 == 0) {
            assume true;
            assume V3;
        }
        if (pc4 == 6) {
            assume true;
            assume !V4 && V5 && !V6;
        } else if (pc4 == 5) {
            assume true;
            assume V5 && !V6;
        } else if (pc4 == 4) {
            assume true;
            assume !V4 && !V5 && !V6;
        } else if (pc4 == 3) {
            assume true;
            assume !V6;
        } else if (pc4 == 2) {
            assume true;
            assume !V4 && !V5;
        } else if (pc4 == 1) {
            assume true;
            assume true;
        } else if (pc4 == 0) {
            assume true;
            assume V4;
        }
        if (pc5 == 2) {
            assume true;
            assume !V4 && !V6;
        } else if (pc5 == 1) {
            assume true;
            assume true;
        } else if (pc5 == 0) {
            assume true;
            assume V6;
        }
        if (pc6 == 0) {
            assume true;
            assume V6;
        }
        if (pc7 == 2) {
            assume minDurG3_X2 <= 10.0;
            assume V6;
        } else if (pc7 == 1) {
            assume true;
            assume !V6;
        } else if (pc7 == 0) {
            assume true;
            assume V6;
        }
        assert (pc2 == 2 && pc3 == 2 ==> minDurG2_X2 >= 15.0 || bndResG1_X2 < 10.0) && (pc2 == 1 && pc3 == 2 ==> minDurG2_X2 >= 15.0 || bndResG1_X2 < 10.0);
        assert (pc4 == 6 && pc6 == 0 ==> false) && (pc4 == 5 && pc6 == 0 ==> false) && (pc4 == 4 && pc6 == 0 ==> false) && (pc4 == 3 && pc6 == 0 ==> false);
        assert (pc4 == 6 && pc7 == 2 ==> minDurG3_X2 >= 10.0) && (pc4 == 5 && pc7 == 2 ==> minDurG3_X2 >= 10.0) && (pc4 == 4 && pc7 == 2 ==> minDurG3_X2 >= 10.0) && (pc4 == 3 && pc7 == 2 ==> minDurG3_X2 >= 10.0);
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
                assume V1';
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
                assume V1';
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
                assume bndResG1_X2 < 10.0;
                pc2 := 2;
            } else if (*) {
                assume bndResG1_X2 < 10.0;
                pc2 := 1;
            } else if (*) {
                assume !V3';
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 1) {
            if (*) {
                assume bndResG1_X2 < 10.0;
                pc2 := 2;
            } else if (*) {
                assume bndResG1_X2 < 10.0;
                pc2 := 1;
            } else if (*) {
                assume !V3';
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
                assume minDurG2_X2 >= 15.0 || V3';
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
        if (pc4 == 6) {
            if (*) {
                assume true;
                pc4 := 6;
            } else if (*) {
                assume true;
                pc4 := 4;
            } else if (*) {
                assume V4';
                pc4 := 5;
            } else if (*) {
                assume V4' && !V5';
                pc4 := 3;
            } else {
                assume false;
            }
        } else if (pc4 == 5) {
            if (*) {
                assume true;
                pc4 := 5;
            } else if (*) {
                assume !V5';
                pc4 := 3;
            } else {
                assume false;
            }
        } else if (pc4 == 4) {
            if (*) {
                assume true;
                pc4 := 6;
            } else if (*) {
                assume true;
                pc4 := 4;
            } else if (*) {
                assume V4';
                pc4 := 5;
            } else if (*) {
                assume V4' && !V5';
                pc4 := 3;
            } else {
                assume false;
            }
        } else if (pc4 == 3) {
            if (*) {
                assume true;
                pc4 := 3;
            } else {
                assume false;
            }
        } else if (pc4 == 2) {
            if (*) {
                assume true;
                pc4 := 6;
            } else if (*) {
                assume true;
                pc4 := 2;
            } else if (*) {
                assume V4';
                pc4 := 5;
            } else if (*) {
                assume V4' && !V5';
                pc4 := 1;
            } else {
                assume false;
            }
        } else if (pc4 == 1) {
            if (*) {
                assume true;
                pc4 := 1;
            } else {
                assume false;
            }
        } else if (pc4 == 0) {
            if (*) {
                assume true;
                pc4 := 0;
            } else if (*) {
                assume true;
                pc4 := 1;
            } else {
                assume false;
            }
        }
        if (pc5 == 2) {
            if (*) {
                assume true;
                pc5 := 2;
            } else if (*) {
                assume !V4' && V6';
                pc5 := 1;
            } else {
                assume false;
            }
        } else if (pc5 == 1) {
            if (*) {
                assume true;
                pc5 := 1;
            } else {
                assume false;
            }
        } else if (pc5 == 0) {
            if (*) {
                assume true;
                pc5 := 0;
            } else if (*) {
                assume true;
                pc5 := 1;
            } else {
                assume false;
            }
        }
        if (pc6 == 0) {
            if (*) {
                assume true;
                pc6 := 0;
            } else {
                assume false;
            }
        }
        if (pc7 == 2) {
            if (*) {
                assume minDurG3_X2 >= 10.0 || V6';
                pc7 := 1;
            } else if (*) {
                assume minDurG3_X2 < 10.0;
                pc7 := 2;
            } else if (*) {
                assume minDurG3_X2 >= 10.0;
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 1) {
            if (*) {
                assume true;
                pc7 := 1;
            } else if (*) {
                assume true;
                minDurG3_X2 := 0.0;
                pc7 := 2;
            } else {
                assume false;
            }
        } else if (pc7 == 0) {
            if (*) {
                assume true;
                pc7 := 1;
            } else if (*) {
                assume true;
                pc7 := 0;
            } else {
                assume false;
            }
        }
        V0 := V0';
        V1 := V1';
        V2 := V2';
        V3 := V3';
        V4 := V4';
        V5 := V5';
        V6 := V6';
    }
}

