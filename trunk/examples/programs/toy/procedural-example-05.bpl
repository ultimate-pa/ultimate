//#Safe
/*
 *
 * Sketch for the chc for the return edge:
 *  signature: 
 *    bar-exit(g, a, b ,c, l)
 *    bef-call(g, x, y, z);
 *    aft-call(g, x, y, z);
 *
 *    bef-call(g, x', y', z) 
 * /\ bar-exit(old-g, g', a, b, c, l) 
 * /\ a = x' /\ b = y'
 * /\ z' = c
 * /\ old-g = g
 *  --> aft-call(g', x', y', z')
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure foo();
modifies g;

implementation foo() {
  var x, z: int;

  x := 1;

  g := 3;

  call z := bar(x);
  
  assert z == 8;
}

procedure bar(a : int) returns (c : int);
modifies g;

implementation bar(a : int) returns (c : int) {
  var l: int;

  l := 4;

  c := a + g + l;

  return;
}

