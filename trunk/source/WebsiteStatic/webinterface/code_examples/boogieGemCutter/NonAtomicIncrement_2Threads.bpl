//#Unsafe
/*
 * Puzzle: We run two threads that increment a global variable concurrently.
 * The increment is not done atomically, between each read and write there may
 * be a context switch. Each thread increments the variable four times.
 * Let us assume that the initial value of the global variable was zero and 
 * each thread is run comletely.
 * Is it possible that the value of the global variable is less than two?
 * The following program shows us the solution to this puzzle.
 * 
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-08-23
 * 
 */

var x : int;

procedure ULTIMATE.start()
modifies x;
{
    x := 0;

    fork 1 IncrementProcess1();
	fork 2 IncrementProcess2();
    join 1;
	join 2;
	assert x >= 3;
}



procedure IncrementProcess1()
modifies x;
{
	var localx : int;
	
		localx := x;
		x := localx + 1;

		localx := x;
		x := localx + 1;

		localx := x;
		x := localx + 1;
}


procedure IncrementProcess2()
modifies x;
{
	var localx : int;
	
		localx := x;
		x := localx + 1;

		localx := x;
		x := localx + 1;

		localx := x;
		x := localx + 1;
}
