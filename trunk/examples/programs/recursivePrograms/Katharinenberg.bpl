//#Safe
/*
 * Example taken from a draft titled
 * "Using Program-specific Summaries in Deductive Verification" 
 * written by 
 * Marius Greitschus, Sergio Feo-Arenis, Bernd Westphal, Daniel Dietsch, 
 * and Andreas Podelski
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 27.05.2013
 */
var x : int;
 
procedure main();
modifies x;

implementation main()
{
  var y,b: int;
  assume (y>=0 && y<=100);
  if (y % 2 != 0) {
    b := 1;
  } else {
    b := 0;
  }
  call f(b,y);
  assert ((y % 2 ==0) ==> (x % 2) != 0 );
}


procedure f(b, a: int) returns ();
modifies x;

implementation f(b, a: int) returns ()
{
  if (b != 0) {
    x := 2*a;
  } else {
    x := 2*a+1;
  }
}