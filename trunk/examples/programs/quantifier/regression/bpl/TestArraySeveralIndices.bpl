//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.4.2012
 * 
 */
procedure proc(b: int);

implementation proc(b: int)
{
  var a:[int,int,int,int]int;
  a[0,1,2,3] := 23;
  assert (a[0,1,2,3] == 23);
}





  
