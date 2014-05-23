//#Safe
/* Shows bug in BackwardPredicats in revision 11541.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 8.5.2014
 *
 */

implementation callee(in_b : int) returns (callee : int)
{
    var nondet_1 : int;
    var t_post0 : int;
    var t_post : int;
    g := in_b;
    t_post := g;
    g := t_post + 1;
    havoc t_post;
    callee := g + 1;
    return;
}

implementation main() returns (main : int)
{
    var x : int;
    var t_ret2 : int;

    x := g;
    call t_ret2 := callee(g + 1);
    g := t_ret2;
    assert x == g - 3;
}

var g : int;

implementation ULTIMATE.start() returns ()
{
    var t_ret3 : int;

    g := 0;
    call t_ret3 := main();
}

procedure callee(in_b : int) returns (callee : int);
    modifies g;

procedure main() returns (main : int);
    modifies g;

procedure ULTIMATE.start() returns ();
    modifies g;

