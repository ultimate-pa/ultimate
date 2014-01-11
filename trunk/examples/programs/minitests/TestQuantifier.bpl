//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 5.5.2012
 */
procedure proc();

implementation proc()
{
  var a:[int]int;
  assume (forall i : int :: a[i] == 0);
  assert (a[0] == 0);
}





  
