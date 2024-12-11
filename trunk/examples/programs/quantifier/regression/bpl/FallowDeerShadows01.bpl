//#Safe
/*
 * Example that I wrote in order to reproduce a shadowing problem.
 * I was not successful because here quantified variables were
 * renamed before the problem could occur. 
 * Nonetheless this example might be helpful.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-21
 */

var i :int;
var a:[int]int;

procedure proc();
modifies i;

implementation proc()
{
  assume (exists i : int :: a[i] == 42);
  while (*) {}
  i := 23;
  while (*) {}
  assert i == 23 && (exists i : int :: a[i] == 42);
}





  
