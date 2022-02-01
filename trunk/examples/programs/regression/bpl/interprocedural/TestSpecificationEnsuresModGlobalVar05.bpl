//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.3.2012
 * 
 * safe or not? ensures of callee is unsatisfiable, since g not modified
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  g:= 0;
  call callee();
  assert ( false );
}

procedure callee() returns ();
ensures g == old(g)+1;


  
