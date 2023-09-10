/*
 * Date: 2020-01-26
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Difficult loop that occurs in example that Daniel sent me.
 *
 */

procedure main() returns ()
{
    var x,y: int;
    while (y < 0 && 2147483647 < ((y + 4294967295) % 4294967296)) {
        y := x;
        x := ((y + 4294967295) % 4294967296) - 4294967296;
    }
}

