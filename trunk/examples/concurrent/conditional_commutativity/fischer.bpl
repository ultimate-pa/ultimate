//#Safe
/*
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Editor: Marcel Ebbinghaus
 *
 * Copy of Fischer.bpl
 * Idea: Safe program which results in nontermination for the DFS-Approach if using the default criterion,
 * but using the limited checks criterion forces termination
 * Furthermore, the DFS-Approach is able to find conditional commutativity
 * (sleep set criterion works best for BySerialNumber)
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
   assume (wait > delay);
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