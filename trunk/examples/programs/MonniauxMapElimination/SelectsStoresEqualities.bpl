/*
 * Date: 2019-04-08
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i : int;
var tmp : int;
var tmp2 : [int]int;


procedure main() returns ()
modifies a, tmp, tmp2;
{
  tmp := a[i];
  tmp2 := a;
  a[i] := 5;
  while (a[0] == tmp2[0]) {
    tmp2[0] := 0;
  }
}




