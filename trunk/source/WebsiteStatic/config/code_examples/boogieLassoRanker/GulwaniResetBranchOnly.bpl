//#rTerminationDerivable
/*
 * Date: 2012-06-14
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Reduced example where only one path through the while loop can be taken.
 * Figure 1 from 
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow Refinement and Progress 
 * Invariants for Bound Analysis.
 * Ex7 from
 * 2012PLDI -  Gulwani,Zuleger - The reachability-bound problem
 * 
 */

procedure cyclic() returns ()
{
  var id,maxId,tmp : int;
  assume 0 < id;
  assume id < maxId;
  while (tmp != id) {
    assume (tmp > maxId);
      tmp := 0;
  }
}
