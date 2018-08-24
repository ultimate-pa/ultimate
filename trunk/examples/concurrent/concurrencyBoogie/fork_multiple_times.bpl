/*
 * A little example that should fail, since ultimate is not able to fork the same procedure multiple times now.
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
    x := 3;
    fork 1 foo(x);
    fork 2 foo(4);
    fork x foo(1);
    
    join x := 1;
    join 2;
    join 3;
}


procedure foo(i : int)
{
    var y : int;
    y := 4;
}