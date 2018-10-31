//#Unsafe
/*
 * This example should show that either one of the cases in the if statement will never be reached yet.
 * 
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 30.10.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var res : int;
    var sum : int;
    sum := 0;
    res := 0;
    x := 0;

    while (x < 3) {
        fork 1 foo();
        join 1 assign res;
        sum := sum + res;
        x := x + 1;
    }
    // Since the local variable of a procedure keeps its old value from the last time it became forked,
    // The sum will either be 15 or 3. So this program should always fail yet.
    assert (sum == 3) || (sum == 15);
}


procedure foo() returns(res : int)
{
    var y : int;
    var x : int;
    
    if (y > x) {
        res := 5;
    } else {
        res := 1;
    }
}
