//#Safe
/*
 * Date: 2019-06-08
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int][int]int;
var i : int;
var j : int;
var tmp : int;
var tmp2 : int;


procedure main() returns ()
modifies a, tmp, tmp2;
{
  a[1][2] := 8;
  tmp := a[1][2];
  a[1][2] := 16;
  tmp2 := a[1][2];
  assert tmp != tmp2;
}




