//#Safe
/*
    Lamport's Bakery with 2 threads
*/

var entering1, entering2: int;
var number1, number2: int;
var crit: int;

procedure ULTIMATE.start()
modifies entering1, entering2, number1, number2, crit;
{
    entering1 := 0;
    entering2 := 0;
    number1 := 0;
    number2 := 0;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies entering1, number1, crit;
{
    entering1 := 1;
    number1 := 1 + (if number2 > number1 then number2 else number1);
    entering1 := 0;

    while (entering2 != 0) {
        // Busy wait
        assume 1 == 1;
    }
    while (number2 != 0 && number2 < number1) {
        assume 1 == 1;
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
    entering2 := 1;
    number2 := 1 + (if number1 > number2 then number1 else number2);
    entering2 := 0;

    while (entering1 != 0) {
        assume 1 == 1;
    }
    while (number1 != 0 && (number1 < number2 || (number1 == number2 && 1 < 2))) {
        assume 1 == 1;
    }

    // Critical section for Thread2.
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;

    number2 := 0;
}
