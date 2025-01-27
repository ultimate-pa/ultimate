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
  a[j] := (if i==0 then 0 else 1); 
  tmp := a[j];
  assert tmp == 0;
}



