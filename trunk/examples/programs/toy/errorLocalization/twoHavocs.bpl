//#Unsafe
/*
 * The second havoc is relevant.
 *
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2017-07-04
 */

procedure main() returns () {
    var x,y: int;
    havoc x;
    havoc y;
    assert x > 0 && y > 0;
}
