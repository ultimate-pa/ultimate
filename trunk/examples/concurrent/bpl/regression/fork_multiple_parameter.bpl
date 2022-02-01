//#Safe
/*
 * Check if forking a procedure with multiple parameter works correctly.
 *
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 21.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : int;
    x := 1;
    y := 2;

    fork 1 add(x, y);
    
    x := 3;
    
    join 1 assign y;
    
    assert y == x;
}

procedure add(num1 : int, num2 : int) returns(sum : int);

implementation add(num1 : int, num2: int) returns (sum : int)
{
    assert num1 == 1;
    sum := num1 + num2;
}
