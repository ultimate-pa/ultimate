//#Unsafe
/*
 * Only the last assignment is relevant in this example.
 *
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2017-07-01
 */

procedure main() returns () {
    var x,y,z: int;

    x := x + y;
    x := y + z;
    x := y + z;
    assert x >= 0;
}
