// #Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-09-11
 *
 */

var g : int;

procedure foo() returns () 
modifies g;
{
    g := g;
}

procedure main() returns ()
modifies g;
{
    var n : int;
    assume (n <= g);
    call foo();
    assert (n <= g);
}