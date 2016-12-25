//#Terminating
/*
 * Resembles modulo arithmetic of unsigned integers in C.
 * We fail to prove termination, no implementation for computing integral hull.
 * Date: 2016-12-13
 * Author: Matthias Heizmann
 * 
 */

procedure main() returns (){
    var x : int;

    assume true;
    while (x % 4 >= 1)
    {
        x := x - 1;
    }
}


