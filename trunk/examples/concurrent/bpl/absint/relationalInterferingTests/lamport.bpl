//#Safe
/*
    Lamport's Bakery with 2 threads
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
    entering1 := true;
    number1 := 1 + (if number2 > number1 then number2 else number1);
    entering1 := false;

    while (entering2) {
        // Busy wait
        assume true;
    }
    while (number2 != 0 && number2 < number1) {
        assume true;
    }

    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;

    number1 := 0;
}

procedure Thread2()
modifies entering2, number2, crit;
{
    entering2 := true;
    number2 := 1 + (if number1 > number2 then number1 else number2);
    entering2 := false;

    while (entering1) {
        assume true;
    }
    while (number1 != 0 && (number1 < number2 || (number1 == number2 && 1 < 2))) {
        assume true;
    }

    // Critical section for Thread2.
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;

    number2 := 0;
}
