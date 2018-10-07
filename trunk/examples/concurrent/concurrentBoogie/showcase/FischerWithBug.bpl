//#Safe
/*
 * Implementation of Fischer's mutual exclusion protocol.
 * 
 * In this buggy implementation, the a process does not spend enough time
 * for its check if the lock has already been aquired by another process.
 * 
 * time that a process needs to set the lock 
 * and the time that a process waits for checking if the lock has been aquired 
 * - 
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-10-03
 *
 */

var lock : int;
var clk : int;
var wait : int;
var delay : int;

// count number of processes in critical section
var critical : int;
 
procedure ULTIMATE.start() returns()
modifies critical, clk, lock;
{
   critical := 0;
   clk := 0;
   assume (wait >= 1);
   // Bug: time for waiting during the check can coincide
   // with the time that is needed to set the lock
   assume (wait >= delay);
   fork 0 Clock();
   fork 1 Process1();
   fork 2 Process2();
}


procedure Clock() returns ()
modifies clk;
{
    while (true) {
	clk := clk +1;
    }

}



procedure Process1() returns ()
modifies critical, lock;
{
  var deadline: int;
  
    while (true) {
	if (lock != 1) {
	    deadline := clk + delay;
	    assume lock == 0;
	    lock := 1;
	    assume clk <= deadline;
	    deadline := clk + wait;
	    assume clk >= deadline;
	    assume lock == 1;
	}
	assert (critical == 0);
	critical := 1;
	critical := 0;
	lock := 0;
    }
}

procedure Process2() returns ()
modifies critical, lock;
{
  var deadline: int;
    while (true) {
	if (lock != 2) {
	    deadline := clk + delay;
	    assume lock == 0;
	    lock := 2;
	    assume clk <= deadline;
	    deadline := clk + wait;
	    assume clk >= deadline;
	    assume lock == 2;
	}
	assert (critical == 0);
	critical := 2;
	critical := 0;
	lock := 0;
    }
}
