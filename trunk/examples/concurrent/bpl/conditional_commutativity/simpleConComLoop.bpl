//#Unsafe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Unsafe program which contains conditional commutativity, which is not implied by the infeasibility proof of
 * the first iteration (which thus needs 3 iterations with BySerialNumber and 4 with LoopLockStep),
 * but will be detected by our conditional commutativity checker
 */



 var x : int;
 var y : int;
 
 
procedure ULTIMATE.start() returns()
modifies x,y;
{
   x := 0;
   fork 0 Process0();
   fork 1 Process1();
}


procedure Process0() returns ()
modifies x,y;
{
  while (true){
    y := x;
	x := x + 1;
 }  

}

procedure Process1() returns ()
modifies x,y;
{
  while (true){
    y := 0;
	assert (y == 0);
	x := x - 1;
  }

}
