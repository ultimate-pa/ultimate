/*
 * Date: 2019-04-08
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i,j : int;


procedure main() returns ()
modifies a,i;
{
  a[i] := 5;
  a[j] := 6;
  assert i==j ==> a[i] == 6;
}




