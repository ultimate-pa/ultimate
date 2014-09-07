//#Safe
/* Shows bug in BackwardPredicats in revision 11541.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 8.5.2014
 *
 */

implementation callee(b : int) returns (callee : int)
{
    g := b + 2;
    callee := g;
    return;
}

implementation main() returns ()
{
    var x : int;
    var tmp : int;

    x := g;
    call tmp := callee(g + 1);
    g := tmp;
    assert x == g - 3;
}

var g : int;

implementation ULTIMATE.start() returns ()
{
    assume true;
    call main();
}

procedure callee(b : int) returns (callee : int);
    modifies g;

procedure main() returns ();
    modifies g;

procedure ULTIMATE.start() returns ();
    modifies g;

