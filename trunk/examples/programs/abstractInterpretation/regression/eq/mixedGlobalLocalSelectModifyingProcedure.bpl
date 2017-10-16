//#Safe
/*
 * Similar to mixedGlobalLocalSelectNonModifyingProcedure.bpl, but here the 
 * modifies clause allows a to be modified by foo. Thus the analysis must 
 * proved that it is not actually modified in order to prove the assertion.
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
modifies a;

implementation foo(y : int) returns (res : int) {
  res := y;
  return;
}

