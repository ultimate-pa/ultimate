//#Unsafe
/*
 * This example shows how fork and join works for different id types.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 22.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : int;
    x := 1;
    y := 1;

    fork 1 foo();
    join x;
    fork y bar();
    
    join 1;
    assert 0 == 1;
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
