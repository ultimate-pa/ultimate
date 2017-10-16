//#Safe
/*
 * Test that should trigger a cycle in CongruenceClosure.projectToElements we 
 * had at some point.
 */
procedure main() {
  var a, b, c : [int] int;
  var i, j, x, y : int;


  assume b == c[i := 4];
  //assume b == c[j := 4];
  assume a[i] == x;
  assume a[i] == a[y];
  assume a[x] == y;
  havoc i;


  assert true;
}
