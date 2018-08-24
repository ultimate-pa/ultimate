/*
 * This example shows, that the fork statement is not working in a loop if it 
 * is not getting joined until the next iteration. Except the loop has only 
 * one iteration. 
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

    while (x < 1) {
        fork x foo(x);
        x := x + 1;
    }
    x := 1;
    while (x < 3) {
        fork x foo(x);
        x := x + 1;
    }
    
    join x;
}


procedure foo(i : int)
{
    var y : int;
    y := 4;
}