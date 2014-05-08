//#Safe
/* Shows bug in BackwardPredicats in revision 11541.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 8.5.2014
 *
 */

implementation callee(#in~b : int) returns (callee : int)
{
    var ~b : int;
    var ~nondet~1 : int;
    var #t~post0 : int;
    var #t~post1 : int;

    ~b := #in~b;
    havoc ~nondet~1;
    ~g := ~b;
    if (~nondet~1 != 0) {
        #t~post0 := ~g;
        ~g := #t~post0 + 1;
        havoc #t~post0;
    } else {
        #t~post1 := ~g;
        ~g := #t~post1 + 1;
        havoc #t~post1;
    }
    callee := ~g + 1;
    return;
}

implementation main() returns (main : int)
{
    var ~x~4 : int;
    var #t~ret2 : int;

    ~x~4 := ~g;
    call #t~ret2 := callee(~g + 1);
    ~g := #t~ret2;
    havoc #t~ret2;
    assert ~x~4 == ~g - 3;
}

var ~g : int;
implementation ULTIMATE.init() returns ()
{
    ~g := 0;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret3 : int;

    call ULTIMATE.init();
    call #t~ret3 := main();
}

procedure callee(#in~b : int) returns (callee : int);
    modifies ~g;

procedure main() returns (main : int);
    modifies ~g;

procedure ULTIMATE.init() returns ();
    modifies ~g;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ~g, ~g;
    modifies ~g;

