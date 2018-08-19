/*
 * Just a little example to demonstrate how the fork and join statements can 
 * be used.
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 09.05.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    x := 4;
    fork 1 foo();
    
    join x := 1;
}


procedure foo() returns(ret : int)
{
    var y : int;
    y := 4;
    
    ret := y;
}
