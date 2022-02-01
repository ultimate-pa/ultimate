//#Safe
/*
 * Date: 2019-05-01
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i : int;
var j : int;
var tmp : int;


procedure main() returns ()
modifies a, tmp, i;
{
  i:=0;
  while (i < 100) {
    if (i <50) {
      a[i] := 0;
    } else {
      a[i] := 1;
    }
    i := i + 1;
  }
  tmp := a[j];
  assert (j < 50 && j >= 0) ==> tmp == 0;
  assert (j >= 50 && j < 100) ==> tmp == 1;
}



