//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * A 4-bit counter. Suggested by Neil Jones.
 * The Program is incorrect according to its (pathological) specification.
 *
 * The Example is interesting for a trace abstraction, because correctness
 * of the n-bit counter ist decideable and we can analyze the worst case
 * complexity of our algorithm.
 * 
 * We need an exponential number of iterations to find a feasible error trace.
 *
 * Also interesting: Change to assertion to assert x3 != 0.
 * Program is now correct but using the naive approach a exponential number of
 * iterations are necessary.
 * However, a small interpolant automaton with states true, x3 !=0, false would be
 * suffcient. 
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

assert x3 == 0;

}
