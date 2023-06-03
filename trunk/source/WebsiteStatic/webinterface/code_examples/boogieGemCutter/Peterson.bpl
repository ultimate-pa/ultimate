//#Safe
/*
 * Implementation of Peterson's algorithm for mutual exclusion
 * https://en.wikipedia.org/wiki/Peterson%27s_algorithm
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-10-03
 *
 */

 var flag0 : int;
 var flag1 : int;
 var turn : int;
 // count number of processes in critical section
 var critical : int;
 
 
procedure ULTIMATE.start() returns()
modifies critical, flag0, flag1, turn;
{
    // At the beginning, no process is in the critical section.
    critical := 0;
    fork 0 Process0();
    fork 1 Process1();
}


procedure Process0() returns ()
modifies critical, flag0, flag1, turn;
{
  var x, y: int;

  while (true) {
    flag0 := 1;
    turn := 1;
    assume (flag1 == 0 || turn == 0);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    flag0 := 0;
  }

}

procedure Process1() returns ()
modifies critical, flag0, flag1, turn;
{
   var a, b: int;
 
   while (true) {
     flag1 := 1;
     turn := 0;
     assume (flag0 == 0 || turn == 1);
       assert (critical == 0);
       critical := 1;
       critical := 0;
     flag1 := 0;
   }

}
