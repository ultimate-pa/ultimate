//#cUnsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 16.12.2011
 *
 * Fischer mutual exclusion algorithm
 */

 var lock : int;
 var critical : int;
 var clk : int;
 var wait : int;
 var delay : int;
 
 
procedure ~init() returns();
modifies critical;
modifies clk;

implementation ~init()
{
   critical := 0;
   clk := 0;
   assume (wait >= 1);
   assume (wait >= delay);
}


procedure Clock() returns ();
modifies clk;
 
implementation Clock()
{
    while (true) {
	clk := clk +1;
    }

}



procedure Thread1() returns ();
modifies critical;
modifies lock;
 
implementation Thread1()
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

procedure Thread2() returns ();
modifies critical;
modifies lock;
 
implementation Thread2()
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