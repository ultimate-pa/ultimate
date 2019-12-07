//#Unsafe
/*
 * 
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-08-23
 * 
 */


procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : int;
    x := 0;

    fork 1 increment(x);
	fork 2 decrement(x);
    join 2 assign y;
	assert y == 1;
}

procedure increment(n : int) returns(res : int);

implementation increment(n : int) returns(res : int)
{
	res := n + 1;
}


procedure decrement(n : int) returns(res : int);

implementation decrement(n : int) returns(res : int)
{
	res := n - 1;
}
