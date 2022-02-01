//#SyntaxError
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 12.3.2012
 * call callee(a) not allowed  if callee has out-paramaters
 * use call x:=callee(a)
 *
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  var c,y: int;
  g:= 0;
  call callee(a);
  assert ( g == a );
}

procedure callee(b: int) returns (res: int);
ensures g==old(g)+b;
//ensures res == x+1;



  
