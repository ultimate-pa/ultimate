//#Safe
/*
    Lamport's Bakery algorithm using Boogie BPL with forks.
*/

var entering1, entering2: bool;
var number1, number2: int;
var crit: int;

procedure ULTIMATE.start()
modifies entering1, entering2, number1, number2, crit;
{
    entering1 := false;
    entering2 := false;
    number1 := 0;
    number2 := 0;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies entering1, number1, crit;
{
    // Entry section for Thread1:
    entering1 := true;
    // Assign ticket: number1 := 1 + max(old number1, number2)
    number1 := 1 + (if number2 > number1 then number2 else number1);
    entering1 := false;

    // Wait until Thread2 has picked its number.
    while (entering2) {
        // Busy wait
        assume true;
    }
    // Wait until either Thread2 is not interested or has a higher ticket.
    // For Thread1 (id = 1), the tie–breaker (comparing (number, id)) is:
    // wait while (number2 != 0 and (number2 < number1))
    while (number2 != 0 && number2 < number1) {
        assume true;
    }

    // Critical section for Thread1.
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;

    // Exit section.
    number1 := 0;
}

procedure Thread2()
modifies entering2, number2, crit;
{
    // Entry section for Thread2:
    entering2 := true;
    // Assign ticket: number2 := 1 + max(old number2, number1)
    number2 := 1 + (if number1 > number2 then number1 else number2);
    entering2 := false;

    // Wait until Thread1 has picked its number.
    while (entering1) {
        assume true;
    }
    // Wait until either Thread1 is not interested or has a lower priority.
    // For Thread2 (id = 2), the waiting loop uses the lexicographic order:
    // wait while (number1 != 0 and ((number1 < number2) or (number1 == number2 and 1 < 2))).
    while (number1 != 0 && (number1 < number2 || (number1 == number2 && 1 < 2))) {
        assume true;
    }

    // Critical section for Thread2.
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;

    // Exit section.
    number2 := 0;
}
