// Program obtained from Hamad Ladan's plugin which transforms PEAs into Boogie programs. 
var bndResU0_X4, bndResU1_X4, bndResU2_X4, inv13_X2, maxDurG4_X1, inv5_X4, maxDurU6_X3, bndResBet7_X4, maxDurG8_X1, maxDurG9_X1, minDurG10_X2, bndResG11_X2, maxDurG12_X1, minDurG13_X2 : real, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12, pc13, pc14 : int, delta : real, V2, V2', V3, V3', V0, V0', V1, V1', V4, V4', V5, V5', V7, V7', V6, V6' : bool;
procedure myProcedure() returns ()
    modifies bndResU0_X4, bndResU1_X4, bndResU2_X4, inv13_X2, maxDurG4_X1, inv5_X4, maxDurU6_X3, bndResBet7_X4, maxDurG8_X1, maxDurG9_X1, minDurG10_X2, bndResG11_X2, maxDurG12_X1, minDurG13_X2, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12, pc13, pc14, delta, V2, V2', V3, V3', V0, V0', V1, V1', V4, V4', V5, V5', V7, V7', V6, V6';
{
    havoc pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12, pc13, pc14;
    assume (((((((((((((((pc0 == 0 || pc0 == 1) || pc0 == 3) && ((pc1 == 0 || pc1 == 1) || pc1 == 3)) && ((pc2 == 0 || pc2 == 1) || pc2 == 3)) && (pc3 == 0 || pc3 == 2)) && (pc4 == 0 || pc4 == 1)) && ((pc5 == 0 || pc5 == 2) || pc5 == 6)) && ((pc6 == 0 || pc6 == 2) || pc6 == 5)) && ((pc7 == 0 || pc7 == 2) || pc7 == 6)) && (pc8 == 0 || pc8 == 1)) && (pc9 == 0 || pc9 == 1)) && (pc10 == 0 || pc10 == 1)) && (pc11 == 0 || pc11 == 2)) && (pc12 == 0 || pc12 == 2)) && (pc13 == 0 || pc13 == 1)) && (pc14 == 0 || pc14 == 1);
    havoc bndResU0_X4, bndResU1_X4, bndResU2_X4, inv13_X2, maxDurG4_X1, inv5_X4, maxDurU6_X3, bndResBet7_X4, maxDurG8_X1, maxDurG9_X1, minDurG10_X2, bndResG11_X2, maxDurG12_X1, minDurG13_X2;
    assume ((((((((((((bndResU0_X4 == 0.0 && bndResU1_X4 == 0.0) && bndResU2_X4 == 0.0) && inv13_X2 == 0.0) && maxDurG4_X1 == 0.0) && inv5_X4 == 0.0) && maxDurU6_X3 == 0.0) && bndResBet7_X4 == 0.0) && maxDurG8_X1 == 0.0) && maxDurG9_X1 == 0.0) && minDurG10_X2 == 0.0) && bndResG11_X2 == 0.0) && maxDurG12_X1 == 0.0) && minDurG13_X2 == 0.0;
    while (*)
    {
        havoc V2', V3', V0', V1', V4', V5', V7', V6', delta;
        assume delta > 0.0;
        bndResU0_X4 := bndResU0_X4 + delta;
        bndResU1_X4 := bndResU1_X4 + delta;
        bndResU2_X4 := bndResU2_X4 + delta;
        inv13_X2 := inv13_X2 + delta;
        maxDurG4_X1 := maxDurG4_X1 + delta;
        inv5_X4 := inv5_X4 + delta;
        maxDurU6_X3 := maxDurU6_X3 + delta;
        bndResBet7_X4 := bndResBet7_X4 + delta;
        maxDurG8_X1 := maxDurG8_X1 + delta;
        maxDurG9_X1 := maxDurG9_X1 + delta;
        minDurG10_X2 := minDurG10_X2 + delta;
        bndResG11_X2 := bndResG11_X2 + delta;
        maxDurG12_X1 := maxDurG12_X1 + delta;
        minDurG13_X2 := minDurG13_X2 + delta;
        if (pc0 == 3) {
            assume bndResU0_X4 <= 30.0;
            assume !V0 && V1 && V2 && !V3;
        } else if (pc0 == 2) {
            assume bndResU0_X4 <= 30.0;
            assume !V0 && ((!V1 && !V3) || (!V2 && !V3));
        } else if (pc0 == 1) {
            assume true;
            assume !V0 && (!V1 || !V2 || V3);
        } else if (pc0 == 0) {
            assume true;
            assume V0;
        }
        if (pc1 == 3) {
            assume bndResU1_X4 <= 60.0;
            assume !V0 && V1 && !V2 && !V3;
        } else if (pc1 == 2) {
            assume bndResU1_X4 <= 60.0;
            assume !V0 && ((!V1 && !V3) || (V2 && !V3));
        } else if (pc1 == 1) {
            assume true;
            assume !V0 && (!V1 || V3 || V2);
        } else if (pc1 == 0) {
            assume true;
            assume V0;
        }
        if (pc2 == 3) {
            assume bndResU2_X4 <= 10.0;
            assume V3 && !V4;
        } else if (pc2 == 2) {
            assume bndResU2_X4 <= 10.0;
            assume !V3 && !V4;
        } else if (pc2 == 1) {
            assume true;
            assume !V3 && !V4;
        } else if (pc2 == 0) {
            assume true;
            assume V4;
        }
        if (pc3 == 2) {
            assume true;
            assume V4 && V5;
        } else if (pc3 == 1) {
            assume inv13_X2 <= 25.0;
            assume !V4 && V5;
        } else if (pc3 == 0) {
            assume true;
            assume !V4;
        }
        if (pc4 == 1) {
            assume maxDurG4_X1 < 30.0;
            assume V4;
        } else if (pc4 == 0) {
            assume true;
            assume !V4;
        }
        if (pc5 == 6) {
            assume true;
            assume V4 && !V5 && !V6 && V7;
        } else if (pc5 == 5) {
            assume true;
            assume !V4 && !V5 && !V6 && V7;
        } else if (pc5 == 4) {
            assume inv5_X4 <= 15.0;
            assume V4 && V5 && !V6 && V7;
        } else if (pc5 == 3) {
            assume inv5_X4 <= 15.0;
            assume !V4 && V5 && !V6 && V7;
        } else if (pc5 == 2) {
            assume true;
            assume V4 && V5 && !V6;
        } else if (pc5 == 1) {
            assume true;
            assume !V4 && V5 && !V6;
        } else if (pc5 == 0) {
            assume true;
            assume !V4 || V6;
        }
        if (pc6 == 6) {
            assume maxDurU6_X3 < 20.0;
            assume V4 && !V6 && V7;
        } else if (pc6 == 5) {
            assume maxDurU6_X3 <= 20.0;
            assume V4 && !V6 && V7;
        } else if (pc6 == 4) {
            assume maxDurU6_X3 < 20.0;
            assume !V4 && !V6 && V7;
        } else if (pc6 == 3) {
            assume maxDurU6_X3 <= 20.0;
            assume !V4 && !V6 && V7;
        } else if (pc6 == 2) {
            assume true;
            assume V4 && !V6 && !V7;
        } else if (pc6 == 1) {
            assume true;
            assume !V4 && !V6 && !V7;
        } else if (pc6 == 0) {
            assume true;
            assume !V4 || V6;
        }
        if (pc7 == 10) {
            assume true;
            assume V4 && !V6 && !V7;
        } else if (pc7 == 9) {
            assume true;
            assume !V4 && !V6 && !V7;
        } else if (pc7 == 8) {
            assume true;
            assume V4 && !V6 && V7;
        } else if (pc7 == 7) {
            assume true;
            assume !V4 && !V6 && V7;
        } else if (pc7 == 6) {
            assume bndResBet7_X4 <= 10.0;
            assume V4 && !V6 && !V7;
        } else if (pc7 == 5) {
            assume bndResBet7_X4 <= 10.0;
            assume !V4 && !V6 && !V7;
        } else if (pc7 == 4) {
            assume bndResBet7_X4 <= 10.0;
            assume V4 && !V6 && V7;
        } else if (pc7 == 3) {
            assume bndResBet7_X4 <= 10.0;
            assume !V4 && !V6 && V7;
        } else if (pc7 == 2) {
            assume true;
            assume V4 && !V6 && V7;
        } else if (pc7 == 1) {
            assume true;
            assume !V4 && !V6 && V7;
        } else if (pc7 == 0) {
            assume true;
            assume !V4 || V6;
        }
        if (pc8 == 1) {
            assume maxDurG8_X1 < 4.0;
            assume V4;
        } else if (pc8 == 0) {
            assume true;
            assume !V4;
        }
        if (pc9 == 1) {
            assume maxDurG9_X1 < 4.0;
            assume V3;
        } else if (pc9 == 0) {
            assume true;
            assume !V3;
        }
        if (pc10 == 2) {
            assume minDurG10_X2 <= 30.0;
            assume !V3;
        } else if (pc10 == 1) {
            assume true;
            assume V3;
        } else if (pc10 == 0) {
            assume true;
            assume !V3;
        }
        if (pc11 == 2) {
            assume true;
            assume !V3 && !V4;
        } else if (pc11 == 1) {
            assume true;
            assume true;
        } else if (pc11 == 0) {
            assume true;
            assume V3;
        }
        if (pc12 == 2) {
            assume bndResG11_X2 <= 1.0;
            assume !V0 && V1 && V2;
        } else if (pc12 == 1) {
            assume bndResG11_X2 <= 1.0;
            assume !V0 && (!V1 || !V2);
        } else if (pc12 == 0) {
            assume true;
            assume (!V1 || !V2) || V0;
        }
        if (pc13 == 1) {
            assume maxDurG12_X1 < 45.0;
            assume V0;
        } else if (pc13 == 0) {
            assume true;
            assume !V0;
        }
        if (pc14 == 2) {
            assume minDurG13_X2 <= 40.0;
            assume V0;
        } else if (pc14 == 1) {
            assume true;
            assume !V0;
        } else if (pc14 == 0) {
            assume true;
            assume V0;
        }
        assert (pc0 == 3 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 3 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc0 == 3 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 3 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc0 == 3 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 3 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 2 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 1 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc0 == 0 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc0 == 3 && pc9 == 1 && pc13 == 1 ==> (maxDurG9_X1 < 4.0 || maxDurG12_X1 < 45.0) || bndResU0_X4 < 30.0) && (pc0 == 2 && pc9 == 1 && pc13 == 1 ==> (maxDurG9_X1 < 4.0 || maxDurG12_X1 < 45.0) || bndResU0_X4 < 30.0);
        assert (pc0 == 3 && pc10 == 2 && pc13 == 1 ==> (minDurG10_X2 >= 30.0 || maxDurG12_X1 < 45.0) || bndResU0_X4 < 30.0) && (pc0 == 2 && pc10 == 2 && pc13 == 1 ==> (minDurG10_X2 >= 30.0 || maxDurG12_X1 < 45.0) || bndResU0_X4 < 30.0);
        assert (pc0 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc0 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc0 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc0 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc0 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc0 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc1 == 3 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 3 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 3 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc1 == 3 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 3 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc1 == 3 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 3 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 2 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 1 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc1 == 0 && pc2 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc1 == 3 && pc9 == 1 && pc13 == 1 ==> (maxDurG9_X1 < 4.0 || maxDurG12_X1 < 45.0) || bndResU1_X4 < 60.0) && (pc1 == 2 && pc9 == 1 && pc13 == 1 ==> (maxDurG9_X1 < 4.0 || maxDurG12_X1 < 45.0) || bndResU1_X4 < 60.0);
        assert (pc1 == 3 && pc10 == 2 && pc13 == 1 ==> (minDurG10_X2 >= 30.0 || maxDurG12_X1 < 45.0) || bndResU1_X4 < 60.0) && (pc1 == 2 && pc10 == 2 && pc13 == 1 ==> (minDurG10_X2 >= 30.0 || maxDurG12_X1 < 45.0) || bndResU1_X4 < 60.0);
        assert (pc1 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc1 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc1 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc1 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc1 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc1 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc2 == 3 && pc3 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 1 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 0 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 2 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 1 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 0 && pc4 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc3 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc3 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc3 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc3 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc5 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc5 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc5 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc6 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc6 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc6 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc7 == 10 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 9 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 8 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 7 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc7 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 10 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 9 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 8 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 7 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 6 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 5 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 4 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 3 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc7 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc8 == 1 ==> (maxDurG4_X1 < 30.0 && maxDurG8_X1 < 4.0) || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc8 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc8 == 1 ==> (maxDurG4_X1 < 30.0 && maxDurG8_X1 < 4.0) || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc8 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc9 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc9 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc9 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc9 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc10 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc10 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc10 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc10 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc10 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc10 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc11 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc11 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc11 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc11 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc12 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc12 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc12 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc12 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc12 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc12 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc13 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc13 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc13 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc13 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc4 == 1 && pc14 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc14 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc4 == 1 && pc14 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc14 == 2 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc14 == 1 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc4 == 1 && pc14 == 0 ==> maxDurG4_X1 < 30.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc5 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc5 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc5 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc5 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc6 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc6 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc6 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc6 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc7 == 10 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 9 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 8 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 7 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 10 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 9 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 8 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 7 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 6 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 5 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 4 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 3 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 2 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 1 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 0 && pc8 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc7 == 10 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 9 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 8 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 7 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc7 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 10 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 9 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 8 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 7 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 6 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 5 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 4 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 3 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc7 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc9 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc9 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc9 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc9 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc10 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc10 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc10 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc10 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc10 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc10 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc11 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc11 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc11 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc11 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc12 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc12 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc12 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc12 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc12 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc12 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc13 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc13 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc13 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc13 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc8 == 1 && pc14 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc14 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 3 && pc8 == 1 && pc14 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc14 == 2 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc14 == 1 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0) && (pc2 == 2 && pc8 == 1 && pc14 == 0 ==> maxDurG8_X1 < 4.0 || bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc9 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc9 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc9 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc9 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc10 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc10 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc10 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc10 == 2 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc10 == 1 && pc11 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc10 == 0 && pc11 == 2 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc11 == 2 && pc12 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc11 == 2 && pc12 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc11 == 2 && pc12 == 0 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc12 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc12 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc12 == 0 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc11 == 2 && pc13 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc11 == 2 && pc13 == 0 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc13 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc13 == 0 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc11 == 2 && pc14 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc11 == 2 && pc14 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 3 && pc11 == 2 && pc14 == 0 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc14 == 2 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc14 == 1 ==> bndResU2_X4 < 10.0) && (pc2 == 2 && pc11 == 2 && pc14 == 0 ==> bndResU2_X4 < 10.0);
        assert (pc2 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc2 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc2 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc2 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc2 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc2 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc3 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc3 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc3 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc3 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc3 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc3 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc3 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc3 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc3 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc4 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc4 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc4 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc4 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc4 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc4 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc5 == 6 && pc6 == 6 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 6 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 6 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 6 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 5 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 5 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 5 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 5 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 4 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 4 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 4 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 4 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 3 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 3 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 3 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 6 && pc6 == 3 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 6 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 6 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 6 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 6 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 5 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 5 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 5 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 5 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 4 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 4 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 4 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 4 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 3 && pc7 == 10 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 3 && pc7 == 9 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 3 && pc7 == 8 ==> maxDurU6_X3 < 20.0) && (pc5 == 5 && pc6 == 3 && pc7 == 7 ==> maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 6 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 6 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 6 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 6 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 5 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 5 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 5 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 5 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 4 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 4 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 4 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 4 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 3 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 3 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 3 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 4 && pc6 == 3 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 6 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 6 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 6 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 6 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 5 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 5 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 5 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 5 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 4 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 4 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 4 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 4 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 3 && pc7 == 10 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 3 && pc7 == 9 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 3 && pc7 == 8 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0) && (pc5 == 3 && pc6 == 3 && pc7 == 7 ==> inv5_X4 >= 15.0 || maxDurU6_X3 < 20.0);
        assert (pc5 == 6 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 6 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 5 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 5 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 4 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 4 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc5 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc5 == 6 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 5 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 4 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc5 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc6 == 6 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 6 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 5 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 5 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 4 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 4 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc6 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc6 == 6 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 5 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 4 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc6 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc7 == 10 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 10 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 9 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 9 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 8 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 8 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 7 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 7 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 6 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 6 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 5 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 5 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 4 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 4 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 3 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 3 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc7 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc7 == 10 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 9 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 8 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 7 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 6 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 5 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 4 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 3 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc7 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc8 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc8 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc8 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc8 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc8 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc8 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc9 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc9 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc9 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc9 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc9 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc9 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc10 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc10 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc10 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc10 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc10 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc10 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc10 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc10 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc10 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc11 == 2 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc11 == 2 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc11 == 1 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc11 == 1 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc11 == 0 && pc12 == 2 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc11 == 0 && pc12 == 1 && pc13 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0);
        assert (pc11 == 2 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc11 == 1 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0) && (pc11 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        assert (pc12 == 2 && pc13 == 1 && pc14 == 2 ==> maxDurG12_X1 < 45.0 || (bndResG11_X2 < 1.0 && (minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0))) && (pc12 == 2 && pc13 == 1 && pc14 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc12 == 2 && pc13 == 1 && pc14 == 0 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc12 == 1 && pc13 == 1 && pc14 == 2 ==> maxDurG12_X1 < 45.0 || (bndResG11_X2 < 1.0 && (minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0))) && (pc12 == 1 && pc13 == 1 && pc14 == 1 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc12 == 1 && pc13 == 1 && pc14 == 0 ==> maxDurG12_X1 < 45.0 || bndResG11_X2 < 1.0) && (pc12 == 0 && pc13 == 1 && pc14 == 2 ==> minDurG13_X2 >= 40.0 || maxDurG12_X1 < 45.0);
        if (pc0 == 3) {
            if (*) {
                assume bndResU0_X4 < 30.0;
                pc0 := 3;
            } else if (*) {
                assume bndResU0_X4 < 30.0;
                pc0 := 2;
            } else if (*) {
                assume V3' || V0';
                pc0 := 1;
            } else if (*) {
                assume true;
                pc0 := 0;
            } else {
                assume false;
            }
        } else if (pc0 == 2) {
            if (*) {
                assume bndResU0_X4 < 30.0;
                pc0 := 3;
            } else if (*) {
                assume bndResU0_X4 < 30.0;
                pc0 := 2;
            } else if (*) {
                assume V3' || V0';
                pc0 := 1;
            } else if (*) {
                assume true;
                pc0 := 0;
            } else {
                assume false;
            }
        } else if (pc0 == 1) {
            if (*) {
                assume true;
                bndResU0_X4 := 0.0;
                pc0 := 3;
            } else if (*) {
                assume true;
                pc0 := 1;
            } else if (*) {
                assume true;
                pc0 := 0;
            } else {
                assume false;
            }
        } else if (pc0 == 0) {
            if (*) {
                assume true;
                bndResU0_X4 := 0.0;
                pc0 := 3;
            } else if (*) {
                assume true;
                pc0 := 1;
            } else if (*) {
                assume true;
                pc0 := 0;
            } else {
                assume false;
            }
        }
        if (pc1 == 3) {
            if (*) {
                assume bndResU1_X4 < 60.0;
                pc1 := 3;
            } else if (*) {
                assume bndResU1_X4 < 60.0;
                pc1 := 2;
            } else if (*) {
                assume V3' || V0';
                pc1 := 1;
            } else if (*) {
                assume true;
                pc1 := 0;
            } else {
                assume false;
            }
        } else if (pc1 == 2) {
            if (*) {
                assume bndResU1_X4 < 60.0;
                pc1 := 3;
            } else if (*) {
                assume bndResU1_X4 < 60.0;
                pc1 := 2;
            } else if (*) {
                assume V3' || V0';
                pc1 := 1;
            } else if (*) {
                assume true;
                pc1 := 0;
            } else {
                assume false;
            }
        } else if (pc1 == 1) {
            if (*) {
                assume true;
                bndResU1_X4 := 0.0;
                pc1 := 3;
            } else if (*) {
                assume true;
                pc1 := 1;
            } else if (*) {
                assume true;
                pc1 := 0;
            } else {
                assume false;
            }
        } else if (pc1 == 0) {
            if (*) {
                assume true;
                bndResU1_X4 := 0.0;
                pc1 := 3;
            } else if (*) {
                assume true;
                pc1 := 1;
            } else if (*) {
                assume true;
                pc1 := 0;
            } else {
                assume false;
            }
        }
        if (pc2 == 3) {
            if (*) {
                assume bndResU2_X4 < 10.0;
                pc2 := 3;
            } else if (*) {
                assume bndResU2_X4 < 10.0;
                pc2 := 2;
            } else if (*) {
                assume true;
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 2) {
            if (*) {
                assume bndResU2_X4 < 10.0;
                pc2 := 3;
            } else if (*) {
                assume bndResU2_X4 < 10.0;
                pc2 := 2;
            } else if (*) {
                assume true;
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 1) {
            if (*) {
                assume true;
                bndResU2_X4 := 0.0;
                pc2 := 3;
            } else if (*) {
                assume true;
                pc2 := 1;
            } else if (*) {
                assume true;
                pc2 := 0;
            } else {
                assume false;
            }
        } else if (pc2 == 0) {
            if (*) {
                assume true;
                bndResU2_X4 := 0.0;
                pc2 := 3;
            } else if (*) {
                assume true;
                pc2 := 1;
            } else if (*) {
                assume true;
                pc2 := 0;
            } else {
                assume false;
            }
        }
        if (pc3 == 2) {
            if (*) {
                assume true;
                pc3 := 2;
            } else if (*) {
                assume true;
                inv13_X2 := 0.0;
                pc3 := 1;
            } else {
                assume false;
            }
        } else if (pc3 == 1) {
            if (*) {
                assume true;
                pc3 := 2;
            } else if (*) {
                assume inv13_X2 < 25.0;
                pc3 := 1;
            } else if (*) {
                assume inv13_X2 >= 25.0;
                pc3 := 0;
            } else {
                assume false;
            }
        } else if (pc3 == 0) {
            if (*) {
                assume true;
                pc3 := 2;
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
                maxDurG4_X1 := 0.0;
                pc4 := 1;
            } else if (*) {
                assume true;
                pc4 := 0;
            } else {
                assume false;
            }
        }
        if (pc5 == 6) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume true;
                inv5_X4 := 0.0;
                pc5 := 4;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume true;
                inv5_X4 := 0.0;
                pc5 := 3;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 5) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume true;
                inv5_X4 := 0.0;
                pc5 := 4;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume true;
                inv5_X4 := 0.0;
                pc5 := 3;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 4) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume inv5_X4 < 15.0;
                pc5 := 4;
            } else if (*) {
                assume inv5_X4 >= 15.0 || V6';
                pc5 := 2;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume inv5_X4 < 15.0;
                pc5 := 3;
            } else if (*) {
                assume inv5_X4 >= 15.0 || V6';
                pc5 := 1;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 3) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume inv5_X4 < 15.0;
                pc5 := 4;
            } else if (*) {
                assume inv5_X4 >= 15.0 || V6';
                pc5 := 2;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume inv5_X4 < 15.0;
                pc5 := 3;
            } else if (*) {
                assume inv5_X4 >= 15.0 || V6';
                pc5 := 1;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 2) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume true;
                pc5 := 2;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume true;
                pc5 := 1;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 1) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume true;
                pc5 := 2;
            } else if (*) {
                assume true;
                pc5 := 5;
            } else if (*) {
                assume true;
                pc5 := 1;
            } else if (*) {
                assume V6';
                pc5 := 0;
            } else {
                assume false;
            }
        } else if (pc5 == 0) {
            if (*) {
                assume true;
                pc5 := 6;
            } else if (*) {
                assume true;
                pc5 := 2;
            } else if (*) {
                assume true;
                pc5 := 0;
            } else {
                assume false;
            }
        }
        if (pc6 == 6) {
            if (*) {
                assume true;
                pc6 := 6;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume true;
                pc6 := 4;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 5) {
            if (*) {
                assume maxDurU6_X3 < 20.0;
                pc6 := 5;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume maxDurU6_X3 < 20.0;
                pc6 := 3;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 4) {
            if (*) {
                assume true;
                pc6 := 6;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume true;
                pc6 := 4;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 3) {
            if (*) {
                assume maxDurU6_X3 < 20.0;
                pc6 := 5;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume maxDurU6_X3 < 20.0;
                pc6 := 3;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 2) {
            if (*) {
                assume true;
                maxDurU6_X3 := 0.0;
                pc6 := 6;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume true;
                maxDurU6_X3 := 0.0;
                pc6 := 4;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 1) {
            if (*) {
                assume true;
                maxDurU6_X3 := 0.0;
                pc6 := 6;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume true;
                maxDurU6_X3 := 0.0;
                pc6 := 4;
            } else if (*) {
                assume true;
                pc6 := 1;
            } else if (*) {
                assume V6';
                pc6 := 0;
            } else {
                assume false;
            }
        } else if (pc6 == 0) {
            if (*) {
                assume true;
                maxDurU6_X3 := 0.0;
                pc6 := 5;
            } else if (*) {
                assume true;
                pc6 := 2;
            } else if (*) {
                assume true;
                pc6 := 0;
            } else {
                assume false;
            }
        }
        if (pc7 == 10) {
            if (*) {
                assume true;
                pc7 := 10;
            } else if (*) {
                assume true;
                pc7 := 8;
            } else if (*) {
                assume true;
                pc7 := 9;
            } else if (*) {
                assume true;
                pc7 := 7;
            } else {
                assume false;
            }
        } else if (pc7 == 9) {
            if (*) {
                assume true;
                pc7 := 10;
            } else if (*) {
                assume true;
                pc7 := 8;
            } else if (*) {
                assume true;
                pc7 := 9;
            } else if (*) {
                assume true;
                pc7 := 7;
            } else {
                assume false;
            }
        } else if (pc7 == 8) {
            if (*) {
                assume true;
                pc7 := 10;
            } else if (*) {
                assume true;
                pc7 := 8;
            } else if (*) {
                assume true;
                pc7 := 9;
            } else if (*) {
                assume true;
                pc7 := 7;
            } else {
                assume false;
            }
        } else if (pc7 == 7) {
            if (*) {
                assume true;
                pc7 := 10;
            } else if (*) {
                assume true;
                pc7 := 8;
            } else if (*) {
                assume true;
                pc7 := 9;
            } else if (*) {
                assume true;
                pc7 := 7;
            } else {
                assume false;
            }
        } else if (pc7 == 6) {
            if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 10;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 6;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 8;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 4;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 9;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 5;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 7;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 3;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 5) {
            if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 10;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 6;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 8;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 4;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 9;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 5;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 7;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 3;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 4) {
            if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 10;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 6;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 8;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 4;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 9;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 5;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 7;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 3;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 3) {
            if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 10;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 6;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 8;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 4;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 9;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 5;
            } else if (*) {
                assume bndResBet7_X4 >= 10.0;
                pc7 := 7;
            } else if (*) {
                assume bndResBet7_X4 < 10.0;
                pc7 := 3;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 2) {
            if (*) {
                assume true;
                bndResBet7_X4 := 0.0;
                pc7 := 6;
            } else if (*) {
                assume true;
                pc7 := 2;
            } else if (*) {
                assume true;
                bndResBet7_X4 := 0.0;
                pc7 := 5;
            } else if (*) {
                assume true;
                pc7 := 1;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 1) {
            if (*) {
                assume true;
                bndResBet7_X4 := 0.0;
                pc7 := 6;
            } else if (*) {
                assume true;
                pc7 := 2;
            } else if (*) {
                assume true;
                bndResBet7_X4 := 0.0;
                pc7 := 5;
            } else if (*) {
                assume true;
                pc7 := 1;
            } else if (*) {
                assume V6';
                pc7 := 0;
            } else {
                assume false;
            }
        } else if (pc7 == 0) {
            if (*) {
                assume true;
                bndResBet7_X4 := 0.0;
                pc7 := 6;
            } else if (*) {
                assume true;
                pc7 := 2;
            } else if (*) {
                assume true;
                pc7 := 0;
            } else {
                assume false;
            }
        }
        if (pc8 == 1) {
            if (*) {
                assume true;
                pc8 := 1;
            } else if (*) {
                assume true;
                pc8 := 0;
            } else {
                assume false;
            }
        } else if (pc8 == 0) {
            if (*) {
                assume true;
                maxDurG8_X1 := 0.0;
                pc8 := 1;
            } else if (*) {
                assume true;
                pc8 := 0;
            } else {
                assume false;
            }
        }
        if (pc9 == 1) {
            if (*) {
                assume true;
                pc9 := 1;
            } else if (*) {
                assume true;
                pc9 := 0;
            } else {
                assume false;
            }
        } else if (pc9 == 0) {
            if (*) {
                assume true;
                maxDurG9_X1 := 0.0;
                pc9 := 1;
            } else if (*) {
                assume true;
                pc9 := 0;
            } else {
                assume false;
            }
        }
        if (pc10 == 2) {
            if (*) {
                assume minDurG10_X2 >= 30.0 || !V3';
                pc10 := 1;
            } else if (*) {
                assume minDurG10_X2 < 30.0;
                pc10 := 2;
            } else if (*) {
                assume minDurG10_X2 >= 30.0;
                pc10 := 0;
            } else {
                assume false;
            }
        } else if (pc10 == 1) {
            if (*) {
                assume true;
                pc10 := 1;
            } else if (*) {
                assume true;
                minDurG10_X2 := 0.0;
                pc10 := 2;
            } else {
                assume false;
            }
        } else if (pc10 == 0) {
            if (*) {
                assume true;
                pc10 := 1;
            } else if (*) {
                assume true;
                pc10 := 0;
            } else {
                assume false;
            }
        }
        if (pc11 == 2) {
            if (*) {
                assume true;
                pc11 := 2;
            } else if (*) {
                assume V3' && !V4';
                pc11 := 1;
            } else {
                assume false;
            }
        } else if (pc11 == 1) {
            if (*) {
                assume true;
                pc11 := 1;
            } else {
                assume false;
            }
        } else if (pc11 == 0) {
            if (*) {
                assume true;
                pc11 := 0;
            } else if (*) {
                assume true;
                pc11 := 1;
            } else {
                assume false;
            }
        }
        if (pc12 == 2) {
            if (*) {
                assume bndResG11_X2 < 1.0;
                pc12 := 2;
            } else if (*) {
                assume bndResG11_X2 < 1.0;
                pc12 := 1;
            } else if (*) {
                assume V0';
                pc12 := 0;
            } else {
                assume false;
            }
        } else if (pc12 == 1) {
            if (*) {
                assume bndResG11_X2 < 1.0;
                pc12 := 2;
            } else if (*) {
                assume bndResG11_X2 < 1.0;
                pc12 := 1;
            } else if (*) {
                assume V0';
                pc12 := 0;
            } else {
                assume false;
            }
        } else if (pc12 == 0) {
            if (*) {
                assume true;
                bndResG11_X2 := 0.0;
                pc12 := 2;
            } else if (*) {
                assume true;
                pc12 := 0;
            } else {
                assume false;
            }
        }
        if (pc13 == 1) {
            if (*) {
                assume true;
                pc13 := 1;
            } else if (*) {
                assume true;
                pc13 := 0;
            } else {
                assume false;
            }
        } else if (pc13 == 0) {
            if (*) {
                assume true;
                maxDurG12_X1 := 0.0;
                pc13 := 1;
            } else if (*) {
                assume true;
                pc13 := 0;
            } else {
                assume false;
            }
        }
        if (pc14 == 2) {
            if (*) {
                assume minDurG13_X2 >= 40.0 || V0';
                pc14 := 1;
            } else if (*) {
                assume minDurG13_X2 < 40.0;
                pc14 := 2;
            } else if (*) {
                assume minDurG13_X2 >= 40.0;
                pc14 := 0;
            } else {
                assume false;
            }
        } else if (pc14 == 1) {
            if (*) {
                assume true;
                pc14 := 1;
            } else if (*) {
                assume true;
                minDurG13_X2 := 0.0;
                pc14 := 2;
            } else {
                assume false;
            }
        } else if (pc14 == 0) {
            if (*) {
                assume true;
                pc14 := 1;
            } else if (*) {
                assume true;
                pc14 := 0;
            } else {
                assume false;
            }
        }
        V2 := V2';
        V3 := V3';
        V0 := V0';
        V1 := V1';
        V4 := V4';
        V5 := V5';
        V7 := V7';
        V6 := V6';
    }
}

