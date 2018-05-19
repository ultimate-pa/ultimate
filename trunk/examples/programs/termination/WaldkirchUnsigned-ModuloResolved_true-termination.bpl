//#Terminating
/*
 * Resembles modulo arithmetic of unsigned integers in C.
 * In this example we manually applied the transformation that we do for
 * modulo operations in order to obtain linear arithmetic formulas or 
 * the LassoRanker.
 * We fail to prove termination, no implementation for computing integral hull.
 * 
 * Date: 2016-12-13
 * Author: Matthias Heizmann
 * 
 * 
 * We use 277 instead of 2^n this allows us to identify this constant in
 * debugging output more quickly.
 * 
 */

procedure main() returns (){
    var x, d, r : int;

    assume true;
    while (true) {
        
        //x % 277 >= 1
        havoc d;
        havoc r;
        assume 0 <= r && r < 277;
        assume x == 277 * d + r;
        assume d >= 1;
        if (r < 1) {
            break;
        }
        x := x - 1;
        havoc d;
        havoc r;
        assume 0 <= r && r < 277;
        assume x == 277 * d + r;
        assume d >= 1;
    }
}
