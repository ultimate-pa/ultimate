//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 20.3.2012
 * 
 */

var g: int;

procedure caller(x: int);
modifies g;

implementation caller(x: int)
{
  var d : int;
  var c : real;
  var e : int;
  var a : int;
  var b : real;
  d := 0;
  c := 0.0;
  a := 1;
  b := 3.0;
  e := 5;
  call d,c := callee(d,c);
  assert (d == 1 && c == 1.0 && a == 1 && b == 3.0 && e == 5);
}

procedure callee(a: int, b: real) returns (c: int, d: real);
modifies g;

implementation callee(a: int, b: real) returns (c: int, d: real)
{
  var e : int;
  c := a + 1;
  d := b + 1.0;
  e := e + 1;
}

  
