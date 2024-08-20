/*
 * Date: 2019-08-09
 * Author: luca.bruder@gmx.de
 * Simple code to test whether or not the monniaux map eliminator needs constraints.
 *
 */

var a : [int]int;
var i,j : int;


procedure main() returns ()
modifies a;
{
  assume j != 1;
  assume a[j] == j;
  a[1] := 1;
  assume i != 1;
  assert a[i] != 1;
}




