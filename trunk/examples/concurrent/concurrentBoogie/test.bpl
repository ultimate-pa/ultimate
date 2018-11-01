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
    fork 1 foo();
    join 1;
    assert 1 == 1;
}


procedure foo()
{
    var y : int;
    y := 4;
}
