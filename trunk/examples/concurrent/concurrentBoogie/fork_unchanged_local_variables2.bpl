//#Unsafe
/*
 * This example shows that non-deterministic local variables
 * 
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 01.11.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var res : int;
    var resOld : int;
    res := 0;
    x := 0;

    while (x < 3) {
        fork x foo();
        resOld := res;
        join 1 assign res;
        if (x > 0) {
            assert resOld == res;
        }
        x := x + 1;
    }
}


procedure foo() returns(res : int)
{
    var y : int;
    res := y;
}