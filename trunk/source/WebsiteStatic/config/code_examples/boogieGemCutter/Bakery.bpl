//#Safe
/*
 * Implementation of Lamport's bakery algorithm for mutual exclusion
 * https://en.wikipedia.org/wiki/Lamport%27s_bakery_algorithm
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-10-03
 *
 */



 var n0 : int;
 var n1 : int;
 // count number of processes in critical section
 var critical : int;
 
 
procedure ULTIMATE.start() returns()
modifies critical, n0, n1;
{
   // At the beginning, no process is in the critical section.
   critical := 0;
   n0 := 0;
   n1 := 1;
   fork 0 Process0();
   fork 1 Process1();
}


procedure Process0() returns ()
modifies critical, n0;
{

  while (true) {
    n0 := n1+1;
    assume (n1 == 0 || n0<n1);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    n0 := 0;
  }

}

procedure Process1() returns ()
modifies critical, n1;
{
 
  while (true) {
    n1 := n0+1;
    assume (n0 == 0 || n1<n0);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    n1 := 0;
  }

}
