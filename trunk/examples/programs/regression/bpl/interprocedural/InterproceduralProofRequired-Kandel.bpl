// #Safe
/* 
 * Variable x not visible in inc, hence we need
 * interprocedural proof.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-18
 *
 */

var g : int;

procedure inc() returns () 
modifies g;
{
    g := g + 1;
}


procedure main() returns ()
modifies g;
{
    var x : int;
    assume (g == x);
    call inc();
    assert (g == x + 1);
}
