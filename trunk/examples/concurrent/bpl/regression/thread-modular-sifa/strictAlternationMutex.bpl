//#Safe
/*
*/

var turn : int;
var crit : int;

procedure ULTIMATE.start()
modifies turn, crit;
{
    havoc turn;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies turn, crit;
{
    assume turn == 0;
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;
    turn := 1;
}

procedure Thread2()
modifies turn, crit;
{
    assume turn == 1;
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;
    turn := 0;
}
