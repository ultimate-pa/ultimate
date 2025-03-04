//#Safe
/*
    Flow-sensitivity needed to correctly handle this. (E.g. Location abstraction-mine2017)
    May also be handled correctly without, but abstractions like Interval could still create
    interference: 3>=x>=1, x = 5. Which will lead to 666 being reached.
*/

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    x := 1;
    fork 1 one();
    if (x == 5) {
        x := 666;
    }
    if (x == 2) {
        x := 3;
    }
}

procedure one()
modifies x;
{
    if (x == 1) {
        x := 2;
    }
    if (x == 3) {
        x := 5;
    }
}
