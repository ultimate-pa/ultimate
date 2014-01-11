//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 20.3.2012
 * 
 * Bug: In procedure callee the local variable c shadows the global variable c.
 * However while computing the formula for the call our CFG2SMT plugin uses the
 * global variable c.
 * 
 */

var c: int;

procedure caller(a: int);

implementation caller(a: int)
{
  var b: int;
  call b := callee(a);
  assert ( a+b>=0 );
}

procedure callee(c: int) returns (d: int);
ensures c+d>=0;




  
