/*
 * This example shows how the fork statement handles multiple parameter.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 21.08.2018
 * 
 */

procedure Main();

implementation Main()
{
    var x : int;
    var y : int;
    x := 1;
    y := 2;

    fork 1 add(x, y);
    
    x := 3;
    
    join y := 1;
    
    assert y == x;
}

procedure add(num1 : int, num2 : int) returns(sum : int);

implementation add(num1 : int, num2: int) returns (sum : int)
{
    sum := num1 + num2;
}