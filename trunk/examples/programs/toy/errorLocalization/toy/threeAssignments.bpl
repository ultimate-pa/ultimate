//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-07-01
 */

procedure main() returns () {
    var x,y,z: int;

    x := x + y;
    x := x + z;
    y := y + z;
    assert x >= 0;
}