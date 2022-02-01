//#Safe
/*
 * Safe because old(g) refers to the value of g at the beginning of
 * callee (not at the beginning of caller)
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.03.2014
 */

var g: int;

procedure caller(a: int);
modifies g;

implementation caller(a: int)
{
  g := 42;
  call callee();
}

procedure callee() returns ();
requires old(g) == 42;



  
