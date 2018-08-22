/*
 * This example shows how fork and join works, if there is no fitting type for
 * the join exepression.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 22.08.2018
 * 
 */

procedure Main();

implementation Main()
{
    var x : int;
    var y : bool;
    x := 1;
    y := true;

    fork y foo();
    
    x := 3;
    
    join x;
    assert false;
}

procedure foo();

implementation foo()
{
    var x : int;
    x := 5;
    x := x + 1;
}