//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: April 2012
 * There is no ensures clause for proc1 that allows to prove correctness of
 * proc0. An appropriate ensures clause of proc1 has to state that
 * - the local g is y+1
 * - the global g is old(g)+2
 */

var g: int;

procedure proc0();
modifies g;

implementation proc0()
{
  var x: int;
  g := 0;
  x := 0;
  call x:= proc1(x);
  assert (x == 1);
  assert (g == 2);
}


procedure proc1(y: int) returns (g: int);
modifies g;

implementation proc1(y: int) returns (g: int)
{
  g := y+1;
  call proc2();
}



procedure proc2();
modifies g;

implementation proc2()
{
  g := g+2;
}