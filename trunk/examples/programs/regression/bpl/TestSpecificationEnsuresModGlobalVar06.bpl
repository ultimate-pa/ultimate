//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.03.2014
 * 
 * since g is not in the modifies clause of the procedure callee, b has to be 0
 * and hence a has to be 0.
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  g:= 0;
  call callee(a);
  assert ( a == 0 );
}

procedure callee(b: int) returns ();
ensures g == old(g)+b;


  
