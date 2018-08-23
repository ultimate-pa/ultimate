/*
 * This example shows how fork and join works, if there is no fitting type for
 * the join exepression.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 22.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : bool;
    y := true;

    fork 1 foo();
    fork y foo();
    
    x := 1;
    
    join x;
    join true;
}

procedure foo();

implementation foo()
{
    var x : int;
    x := 5;
    x := x + 1;
}
