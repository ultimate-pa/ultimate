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

  x := #memory_int[p];
  y := #memory_int[q];
  
  assert x == 5;
}
