//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * 
 * 
 */

var g: int;

procedure proc();
modifies g;

implementation proc()
{
  g := g+1;
  assert ( g == old(g) );
}




  
