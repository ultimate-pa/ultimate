//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Correct variant of the 4-bit counter example.
 *
 * In a naive/simple implementation of Trace Abstraction an exponential number of
 * iterations is necessary to prove the correctness.
 * However, a small interpolant automaton with states true, x3 !=0, false would be
 * suffcient to prove the correctness.
 *
 */


procedure FourBitCounter()
{
   var x0, x1, x2, x3: int;

x0 := 0;
x1 := 0;
x2 := 0;
x3 := 0;

while (x3 == 0)
{
   if (x0 == 0) { x0:=1; }
   else 
      {
      x0 := 0;
      if (x1 == 0) { x1:=1; }
      else 
         {
         x1 := 0;
         if (x2 == 0) { x2:=1; }
         else
            {
            x2 := 0;
            if (x3 == 0) { x3:=1; }
            else 
               {
               x3 :=0;
               }            
            }
         }
      }
}

assert x3 != 0;

}
