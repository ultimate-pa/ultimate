//#Safe
/*
 * For each assert statement a contract has to be inferred.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 25.04.2012
 */

var g: int;

procedure caller();
modifies g;

implementation caller()
{
  var x:int;
  g := 0;
  call x:= callee(0);
  assert g == 1;
  assert x == 2;
}

procedure callee(y:int) returns (z:int);
modifies g;

implementation callee(y:int) returns (z:int)
{
  g:=g+1;
  z:=y+2;
}
  
