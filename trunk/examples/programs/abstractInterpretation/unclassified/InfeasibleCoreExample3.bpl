//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-02-04

var a,b : [int]bool;
var x : int;
var p : int;

/*
 * (array!) loop invariant: a == b
 */
procedure checkMemleak() returns () 
modifies a,b,x,p;
{
  b := a; // (= b a)
  x := 0; // (= b a)
  while(*) {
    havoc p;
    assume (a[p] == false); // (and (= (select a k) false) (= b a))
    a[p] := true; // (and (not (select b k)) (= a (store b k true)))
    x := x + 1; // (exists ((p Int)) (and (not (select a p)) (= b a)))
    a[p] := false; // (and (= (select a p) false) (= b a))
  }
  assert(a == b);
}