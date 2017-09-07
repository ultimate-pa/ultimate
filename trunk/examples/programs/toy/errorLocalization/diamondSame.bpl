//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-30
 */

implementation main() returns () {
    var x: int;

    if (x > 0) {
        x := 0;
    } else {
        x := 0;
    }
    assert false;
}

procedure main() returns ();
modifies ;
modifies ;