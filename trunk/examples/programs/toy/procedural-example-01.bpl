
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

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start() {
  var x, y, z: int;

  x := 1;
  y := 2;

  g := 3;

  call z := bar(x, y);
  
  assert z == 10;
  assert g == 1000;
}

procedure bar(a : int, b : int) returns (c : int);
modifies g;

implementation bar(a : int, b : int) returns (c : int) {
  var l: int;

  l := 4;

  c := a + b + g + l;

  g := 1000;

  return;
}

