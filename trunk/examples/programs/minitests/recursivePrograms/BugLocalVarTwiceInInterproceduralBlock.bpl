//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 21.04.2012
 * 
 * Bug in BlockEncoding in r8595.
 * Problem using the current intraprocedural sequential composition for call
 * and return. Local var x occurs twice in code block but we need two 
 * different instances.
 */
var g:int;

procedure main()
modifies g;
{
  g := 23;
  call doNothing();
  g := 42;
  call doNothing();
  assert false;
}


procedure doNothing()
{
  var x:int;
  assume (x == g);
}
