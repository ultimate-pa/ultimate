//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 12.3.2012
 *
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  var c,y: int;
  g:= 0;
  call c := callee(y, a);
  assert ( g == a );
}

procedure callee(x, b: int) returns (res: int);
modifies g;
ensures g==old(g)+b;
ensures res == x+1;



  
