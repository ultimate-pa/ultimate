// Candidates for the examples that explain our construction of inductive
// state assertions.
//
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-01-31

  var a,b : [int]bool;
  var k,j : int;

/*
 * (array!) loop invariant: a == b
 */
procedure noMemleak() returns () 
modifies a,b,k;
{
  b := a; // (= b a)
  k := 0; // (= b a)
  while(*) {
    assume (a[k] == false); // (and (= (select a k) false) (= b a))
    a[k] := true; // (and (not (select b k)) (= a (store b k true)))
    a[k] := false; // (and (= (select a k) false) (= b a))
    k := k + 1; // (exists ((v_k_9 Int)) (and (not (select a v_k_9)) (= b a)))
  }
  assert(a == b);
}



// /*
//  * loop invariant: a[0] == 42
//  */
// procedure firstElementUntouched() returns () {
//   var a : [int]int;
//   var k : int;
//   var x : int;
//   a[0] := 42;
//   assume k>=0;
//   assume k<=0;
//   while(*) {
//     k := k + 1;
//     havoc x;
//     a[k] := x;
//   }
//   assert(a[0] == 42);
// }
// 
// 
// 
// 
// /*
//  * (nonlinear!) loop invariant: x*tmp>0
//  * live variable analysis needed
//  */
// procedure nonlinearInvariant() returns ()
// {
//   var x,y: int;
//   var tmp: int;
//   var k: int;
//   
//   assume (x * y > 0);
//   tmp := y;
//   while (*) {
//     tmp := (if (tmp>=0) then tmp+1 else tmp-1);
//     y := y + 1;
//   }
//   assert (x>=0 ==> tmp>=0);
// }
// 
// 
// /*
//  * loop invariant: x == 0
//  */
// procedure slicing() returns () {
//   var x,k : int;
//   x := 0;
//   k := 0;
//   while(*) {
//     k := k + 1;
//   }
//   assert(x == 0);
// }
// 
// 
// /*
//  * loop invariant: k >= 0
//  */
// procedure sign() returns () {
//   var k : int;
//   assume k>=0;
//   assume k<=0;
//   while(*) {
//     k := k + 1;
//   }
//   assert(k != -1);
// }
// 
// 
// /*
//  * Live variable analysis needed!
//  * loop invariant: x == 0
//  */
// procedure LandesVersicherungsAnstalt() returns () {
//   var x,k : int;
//   k := 0;
//   x := k;
//   while(*) {
//     k := k + 1;
//   }
//   assert(x == 0);
// }
// 
// 
// 
// 
// /*
//  * Why do we replace assignments that are not in the infeasible core by havoc
//  * and not by skip?
//  * Consider the following trace
//  *     y := 0; x := y; y := y + 1; assert(x == 0);
//  * Positions 0,1,3 constitute an infeasible core.
//  * If we would drop position 2, we would obtain the state assertion
//  * y==0&&x==y at nondeterministic if. As a consequence we would conlude
//  * that the second assert statement holds.
//  * 
//  */
// procedure replaceAssingmentByHavoc() returns () {
//   var x,y : int;
//   y := 0;
//   x := y;
//   y := y + 1;
//   if (*) {
//     assert(x == 0);
//   } else {
//     assert(y == 0);
//   }
// }
// 
// 
// 
// 
