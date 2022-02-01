//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 */
procedure proc();

implementation proc()
{
  var a:[int]int;
  var b:[int]int;
  a[0] := 23;
  b[a[0]] := 42;
  a[0] := 7;
  assert (b[23] == 42);
}





  
