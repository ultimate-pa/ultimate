/*
 * We want to assert `x := 5` but not `i:= i + 1`
 *
 * Date: 2025-06-22
 * Author: Matthias Heizmann
 */
implementation main() returns ()
{
    var i, x, y : int;

    y := 0;
    i := 0;
    while(i <= 1000) {
        i := i + 1;
        havoc y;
        x := 5;
    }
    assert y == 0 || x == 5;
}

procedure main() returns ();
