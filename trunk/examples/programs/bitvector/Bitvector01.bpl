//#Safe
/* 
 *
 */

var myVariable:bv20;

procedure proc(n: int) returns ();

implementation proc(n: int) returns ()
{
  var myVariable2:bv20;
  myVariable2 := myVariable;
  if (n >= 0) {
//       call proc(n-1);
//       call proc(n+1-2);
  }
}

