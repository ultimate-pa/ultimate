/*
 * Date: 2019-04-08
 * Author: luca.bruder@gmx.de
 * Simple code to test the monniaux map eliminator.
 *
 */

var a : [int]int;
var i,j,tmp,tmp2 : int;


procedure main() returns ()
modifies tmp, tmp2;
{
  tmp := a[i];
  tmp2 := a[j];
  assert i == j ==> tmp == tmp2;
}




