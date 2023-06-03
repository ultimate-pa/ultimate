//#rTermination
/*
 * Date: 07.10.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * Amir M. Ben-Amram. Size-change termination, monotonicity constraints and
 * ranking functions. Logical Methods in Computer Science, 6(3), 2010.
 * Example 2.3
 *
 */

procedure main() returns () {
    var x,y,z: int;
    while (x > 0 && y > 0 && z > 0) {
        if (y > x) {
            y := z;
            havoc x;
            z := x - 1;
        } else {
            z := z - 1;
            havoc x;
            y := x - 1;
        }
    }
}

