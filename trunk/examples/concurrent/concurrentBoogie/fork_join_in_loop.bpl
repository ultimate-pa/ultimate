//#Unsafe
/*
 * A little example to show that the verification of fork statements in a loop work
 * iff there is also a join statement in the same loop.
 * 
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 24.08.2018
 * 
 */

var n: int;

procedure ULTIMATE.start();
modifies n;

implementation ULTIMATE.start()
{
    var x : int;
    x := 1;

    while (x < 3) {
        fork x foo(x);
        join x;
        x := x + 1;
    }
    assert false;
    join x;
}


procedure foo(i : int)
{
    var y : int;
    y := 4;
}
