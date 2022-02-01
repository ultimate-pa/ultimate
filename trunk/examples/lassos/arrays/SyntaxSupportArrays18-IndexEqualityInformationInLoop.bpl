//#rTermination
/*
 * In 11902 we fail to prove termination because the DNF constructed by
 * RewriteArrays is too large.
 * In more recent revisions we check equality/distinctness in advance and are 
 * hence able to reduce the number of disjuncts significantly.
 * Date: 2014-06-29
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var i,j,k : int;

procedure main() returns ()
modifies a;
{
  while (a[i] >= 0) {
    a[j] := a[j] - 1;
    a[k] := a[k] + 1;
    assume i == j;
    assume i != k;
  }
}

