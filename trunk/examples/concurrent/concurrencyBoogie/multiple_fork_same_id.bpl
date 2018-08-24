/*
 * This example shows how fork and join works for different types as expression.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 24.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : bool;
    x := 1;
    y := true;

    fork 1 foo();
    fork 1 bar();
    
    join x;
}

procedure foo();

implementation foo()
{
    var x : int;
    x := 5;
    x := x + 1;
}

procedure bar();

implementation bar() {
    var x : int;
    x := 5;
    x := x + 1;
}