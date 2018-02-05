//#Safe
/*
 * expected partitioning result: 2 blocks
 */
var #memory_int, #valid : [int] int;

procedure main();
modifies #memory_int, #valid;

implementation main() {
  var p, q, p1, q1, x, y : int;

  assume p != q;
 
  #memory_int[p] := 5;
  #memory_int[q] := 7;

  assume p1 == p && q1 == q;

  x := #memory_int[p1];
  y := #memory_int[q1];
  
  assert x == 5;
}
