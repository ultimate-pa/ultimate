//#Safe
/* Date: 2017-05-12
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Program that shows some problems with invariant synthesis.
 * 
 * If we switch off the over/underapproximation constraints,
 * we have sometimes single locations in the unsat core.
 * We always presumed that this is impossible and that we can
 * have only paths from init to error in the unsat core.
 * 
 * As a consequence we increase the templates at some locations
 * too fast and fail to synthesize an invariant. 
 * 
 */

var x,y,z : int;

procedure main() returns ()
modifies x,y,z;
{
  
  assume(x >= 0 && y >= 0 && z >= 0);
  BranchLoc:
  goto LoopLoc1, LoopLoc2;
  LoopLoc1:
  goto AssertLoc, LoopLoc1;
  LoopLoc2:
  goto AssertLoc, LoopLoc2;
  AssertLoc:
  assert(x >= 0 && y >= 0 && z >= 0);
}


