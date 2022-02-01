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
var tmp2 : int;
var tmp3 : int;
var tmp4 : int;


procedure main() returns ()
modifies a, tmp, tmp2, tmp3, tmp4;
{
  a[i] := 1;
  tmp := a[i];
  a[i] := 2;
  tmp2 := a[i];
  a[i] := 5;
  tmp3 := a[i];
  a[i] := 10;
  tmp4 := a[i];
  a[i] := 20;
  assert tmp!=tmp2;
  assert tmp!=a[i];
  assert a[i]!=tmp2;
}




