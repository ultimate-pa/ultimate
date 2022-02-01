//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.3.2012
 * 
 * safe because g not modified by callee
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  g:= 0;
  call callee();
  assert ( g == 0 );
}

procedure callee() returns ();




  
