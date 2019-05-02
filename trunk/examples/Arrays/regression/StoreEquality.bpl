//#Safe
/*
 * Date: 2019-05-01
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i : int;
var tmp : int;


procedure main() returns ()
modifies a, tmp, i;
{
  i := 5;
  a[5] := 1;
  tmp := a[i];
  assert a[i]==a[5];
  assert tmp==1;
  assert a[i]==1;
  assert a[i]==tmp;
}



