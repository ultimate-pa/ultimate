//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * Example where the invariant derived by my predicate abstractions contains
 * an ArrayStoreExpression.
 * 
 */
procedure proc();

implementation proc()
{
  var a:[int]int;
  var b:[int]int;
  a[0] := 23;
  b[0] := a[0];
  assert (b[0] == 23);
}





  
