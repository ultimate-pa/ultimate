//#Unsafe
/*
 * Just a little example to demonstrate how the fork and join statements can 
 * be used.
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 09.05.2018
 * 
 * Check that some thread can be joined, execution continues after join.
 * (assert false is reachable)
 */

var n: int;

procedure ULTIMATE.start();
modifies n;

implementation ULTIMATE.start()
{
    var x : int;
    x := 1;
    fork 1 foo();
    n := 2;
    
    join x;
    x := 4;
    assert false;
}

procedure foo();
modifies n;

implementation foo()
{
    n := 1;
}

procedure bar();
modifies n;

implementation bar()
{
    n := 2;    
}
