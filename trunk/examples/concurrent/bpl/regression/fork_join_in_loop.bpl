//#Safe
/*
 * A little example to show that the verification of fork statements in a loop work
 * iff there is also a join statement in the same loop.
 * 
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 24.08.2018
 * 
 * Check if we can create threads in a loop if we join them in the same iteration.
 * And if we created a thread of id 1 and join this thread two times that the second join just waits and we do not reach the lines after that join.
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
    x := 1;
    join x;
    /* Can't reach this line since there is no thread left to join */
    assert false;
}


procedure foo(i : int)
{
    var y : int;
    y := 4;
}
