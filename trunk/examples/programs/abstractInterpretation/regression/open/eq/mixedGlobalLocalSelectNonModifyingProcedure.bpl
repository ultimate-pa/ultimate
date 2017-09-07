//#Safe
/*
 * test related to issue #206.
 * In this case that the assertion holds can be inferred from the fact that foo, 
 * by the modifies clause, does not modify a (and that x is  * not modified at 
 * all).
 *
 * author: Alexander Nutz
 */

var a : [int] int;

procedure main ();
modifies a;

implementation main () {
  var x, y : int;

  a[x] := 3;
  
  call y := foo(x);

  assert a[x] == 3;
}

procedure foo(y : int) returns (res : int);
modifies;

implementation foo(y : int) returns (res : int) {
  res := y;
  return;
}

