//#Safe
/*
   Peterson's mutual exclusion algorithm, needs precise abstraction to prove.
   Mine(2017) solves this with location abstraction (in combination with relational interferences).
*/

var b1, b2, turn: bool;
var crit: int;

procedure ULTIMATE.start()
modifies b1, b2, turn, crit;
{
    b1 := false;
    b2 := false;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies b1, turn, crit;
{
    b1 := true;
    turn := false;
    assume (!b2 || turn);
    // critical section
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;
    b1 := false;
}

procedure Thread2()
modifies b2, turn, crit;
{
    b2 := true;
    turn := true;
    assume (!b1 || !turn);
    // critical section
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;
    b2 := false;
}
