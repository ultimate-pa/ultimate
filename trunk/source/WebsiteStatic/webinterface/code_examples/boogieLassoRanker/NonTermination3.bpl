//#rNonTermination
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * 
 */

procedure main() returns ()
{
  var a: [int] int;
  var i: int;
  while (0 <= i && i < 10 && a[i] >= 0) {
    havoc i;
    a[i] := 0;
  }
}
