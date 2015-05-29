//#rTermination
/*
 * In r14388 RewriteArrays fails with "arrayInVar of foreign 
 * index has to be first generation of array".
 * RewriteArrays wants to add the "foreign index" (1 - 1) to
 * array a, however c is considered as first generation
 * of the equivalent arrays a,b,c.
 *
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a,b,c : [int] int;
var x : int;

procedure main() returns ()
modifies a, b, c, x;
{
  assume a[1 - 1] >= 1;
  while (x >= 0) {
    assume a == b;
    assume c == b;
    x := x - c[0];
  }
}

