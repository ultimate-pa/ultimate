//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 03.11.2013
 * 
 * Because of the "initial old(g)=g bug" we added the start procedure to test 
 * this.
 * 
 * 
 */

var g: int;

procedure proc();
modifies g;

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start()
{
  call proc();
}

implementation proc()
{
  g := g+1;
  assert ( g == old(g)+1 );
}




  
