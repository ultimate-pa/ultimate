var flag1, flag2: bool;
var turn: bool;
var crit: int;

procedure ULTIMATE.start()
modifies flag1, flag2, turn, crit;
{
    flag1 := false;
    flag2 := false;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies flag1, flag2, turn, crit;
{
    flag1 := true;
    while(flag2)
    {
        if(turn == true)
        {
            flag1 := false;
            while(turn == true) { assume true; }
            flag1 := true;
        }
    }
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;
    turn := true;
    flag1 := false;
}

procedure Thread2()
modifies flag1, flag2, turn, crit;
{
    flag2 := true;
    while(flag1)
    {
        if(turn == false)
        {
            flag2 := false;
            while(turn == false) { assume true; }
            flag2 := true;
        }
    }
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;
    turn := false;
    flag2 := false;
}
