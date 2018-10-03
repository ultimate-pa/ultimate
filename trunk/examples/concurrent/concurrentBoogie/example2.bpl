// #Safe
/*
 * Just a little example to demonstrate how the fork and join statements can 
 * be used.
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 09.05.2018
 * 
 * We check that return values are passed correctly.
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    x := 5;
    fork 1 foo();
    
    join 1 assign x;

    assert x == 4;
}


procedure foo() returns(ret : int)
{
    var y : int;
    y := 4;
    
    ret := y;
}
