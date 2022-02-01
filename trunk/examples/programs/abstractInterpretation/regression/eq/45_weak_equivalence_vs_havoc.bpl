//#Safe
/*
 * Say we are in a state
 *  a --q=i-- b /\ c[i] = 3
 * and we execute
 *  havoc i
 * then we want to have the following post state
 *  a --c[q]=3-- b
 *
 * author: nutz@informatik.uni-freiburg.de
 */
procedure main() {
  var a, b, c : [int] int;
  var i, j, x : int;

  a := b[i := x];
  c[i] := 3;

  havoc i;
 
  assume c[j] != 3;
  assert a[j] == b[j];
}
