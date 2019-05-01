/*
 * Date: 2019-05-01
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i : int;
var tmp : int;
var tmp2 : int;


procedure main() returns ()
modifies a, tmp, tmp2;
{
  a[i] := 1;
  tmp := a[i];
  a[i] := 2;
  tmp2 := a[i];
  a[i] := 5;
  assert tmp!=tmp2;
  assert tmp!=a[i];
  assert a[i]!=tmp2;
}




