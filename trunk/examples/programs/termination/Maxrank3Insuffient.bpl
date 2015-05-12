// 2015-05-12, Matthias Heizmann
// Example where the automata used for the maxrank3 setting
// are not suffcient. This example is a simplified version of
// PodelskiRybalchenko-TACAS2011-Fig3_true-termination.c
//

procedure main() returns () {
    var x : int;
    var y : int;

    while (x > 0 && y > 0)
    {
        if (*) {
            y := x;
            x := x - 1;
        } else {
            x := y - 1;
            y := y - 1;
        }
    }
}

