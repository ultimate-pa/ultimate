//#Unsafe
/*
 * We developed an extension of the Boogie specification language that can 
 * model systems that run several procedures concurrently.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-08-24
 * 
 */


procedure ULTIMATE.start()
{
    var x : int;
    var y : bool;

    // fork three threads, each has thread id 42
    fork 42 increment(7);
    fork 42 increment(23);
    fork 42 increment(39);
    
    // we join some thread that has id 42
    join 42 assign x;

    // this assert may fail because the thread that we forked
    // second neither returns 8 nor 40.
    assert (x == 8 || x == 40);
}


procedure increment(n : int) returns(res : int)
{
	res := n + 1;
}
