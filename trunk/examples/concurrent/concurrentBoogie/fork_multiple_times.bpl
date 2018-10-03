// #Safe
/*
 * Check that we support several forked threads if each one was
 * forked by a different fork statement.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com), Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
    
    join 1 assign x;
    join 2;
    join 3;
    assert x == 4;
}


procedure foo(i : int)
{
    var y : int;
    y := 4;
}
