//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-11-05
 */

procedure main() returns (){
    var a : int;
    var b : int;

    a := -1;
    b := a % 65536;
    assert(b % 18446744073709551616 == 65535);

    return;
}