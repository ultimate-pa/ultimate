// #Safe
/* 
 * Seems to be bug in quantifier elimination for reals.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-02
 *
 */

procedure ULTIMATE.start() returns (){
    call main();
}

procedure main() returns (){
    var x : real;
    var y : real;

    x := 1.2;
    y := 1.2;
    if (x != y) {
        assert false;
    }
    return;
}
