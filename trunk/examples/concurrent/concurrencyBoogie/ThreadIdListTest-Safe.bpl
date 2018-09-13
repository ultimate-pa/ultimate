//#Safe
/* 
 * Safe because there is thread that was forked with thread ID 2
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-09-12
 * 
 */


procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : int;
    x := 0;

    fork 1 increment(x);
	fork 2, 23 decrement(x);
    join 2 assign y;
	assert false;
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
