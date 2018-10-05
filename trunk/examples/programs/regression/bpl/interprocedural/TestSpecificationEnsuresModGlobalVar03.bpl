//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.3.2012
 * 
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  g:= 0;
  call callee();
  assert ( g == 1 );
}

procedure callee() returns ();
modifies g;
ensures g == old(g)+1;


  
