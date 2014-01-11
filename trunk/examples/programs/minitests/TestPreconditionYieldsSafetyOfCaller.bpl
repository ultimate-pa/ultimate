//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 20.3.2012
 * 
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  call callee();
  assert ( g >= 0 );
}

procedure callee() returns ();
free requires g==0;




  
