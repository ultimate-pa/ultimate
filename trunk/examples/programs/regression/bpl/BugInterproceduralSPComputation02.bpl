//#Safe
/*
 * Date: 08.10.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Bug in computation of Strongest Postcondition in r9797
 */

var x : int;
var y : int;


implementation proc1() returns ()
{
    x := y;
}

implementation main() returns ()
{
    y := 1;
    x := y;
    call proc1();
    call proc2();
}



implementation proc2() returns ()
{
    assume (x != y);
    assert false;
}


procedure proc1() returns ();
    modifies x;


procedure main() returns ();
    modifies x, y;

procedure proc2() returns ();
    modifies x;


procedure ULTIMATE.start() returns ();
    modifies x, y;

implementation ULTIMATE.start() returns ()
{
    call main();
}

