//#Safe
/*
   Peterson's mutual exclusion algorithm, needs precise abstraction to prove.
   Mine(2017) solves this with location abstraction (in combination with relational interferences).
*/

var b1, b2, turn: int;
var crit: int;

procedure ULTIMATE.start()
modifies b1, b2, turn, crit;
{
    b1 := 0;
    b2 := 0;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies b1, turn, crit;
{
    b1 := 1;
    turn := 0;
    assume (b2 == 0 || turn == 1);
    // critical section
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;
    b1 := 0;
}

procedure Thread2()
modifies b2, turn, crit;
{
    b2 := 1;
    turn := 1;
    assume (b1 == 0 || turn == 0);
    // critical section
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;
    b2 := 0;
}
