//#Safe
/*
 * When projecting a variable, then all nodes that depend on it must be removed, too.
 * This includes 
 *  1 its transitive pare
 *  2 non atomic nodes depending on it
 *  3 the transitive parents of the nodes from 2
 * Item 3 was missing at some point, this is the corresponding regression test.
 */
procedure main() {
  var x : int;
  var a : [int] int;
  
  x := a[x + 1];
  havoc x;

  // we don't care for the specification here, only for crashes
  assert true;
}
