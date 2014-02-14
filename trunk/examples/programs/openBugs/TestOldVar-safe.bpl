//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * 
 * Bug: old(g)=g is only assumed at calls and not as initial variable 
 * valuation of procedure
 * 
 * 
 */

var g: int;

procedure proc();
modifies g;

implementation proc()
{
  g := g+1;
  assert ( g == old(g)+1 );
}




  
