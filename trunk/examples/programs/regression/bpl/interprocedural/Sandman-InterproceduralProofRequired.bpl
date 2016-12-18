// #Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-18
 *
 */

var g : int;

procedure inc() returns () 
modifies g;
{
    g := g+1;
}

procedure main() returns ()
modifies g;
{
    var x : int;
    assume (x == g);
    call inc();
    assert (x + 1 == g);
}
