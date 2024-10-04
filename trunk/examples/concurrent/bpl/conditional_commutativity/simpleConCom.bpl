//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Safe program which contains conditional commutativity, which is not implied by the infeasibility proof of
 * the first iteration (which thus needs 2 iterations), but will be detected by our conditional commutativity checker
 * This is only the case for the order BySerialNumber, not for LoopLockStep
 */



 var x : int;
 var y : int;
 
 
procedure ULTIMATE.start() returns()
modifies x,y;
{
   x := 0;
   fork 0 Process0();
   fork 1 Process1();
   join 0;
   join 1;
   x := 1;
   assert (y==0);
}


procedure Process0() returns ()
modifies y;
{
  y := x;
}

procedure Process1() returns ()
modifies y;
{
  y := 0;
}
