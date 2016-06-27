//#Safe
/*
 * Test of multiple assignments.
 */

procedure ULTIMATE.start()
{
   var x, y : int;

   x, y := 1, 2;

   assert (x == 1 && y == 2);
}
