//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-07-23
 * 
 * ProcedureInliner crashes if non-global variable occurs in `old` expression.
 * 
 * Bug pointet out by Martin.
 * https://github.com/ultimate-pa/ultimate/issues/640
 *
 */

var glob : int;

procedure foo(x : int) returns ( result : int)
ensures result == old(glob + x);
modifies glob;
{
  result := glob + x;
  glob := glob + 1;
  return;
}

procedure ULTIMATE.start() returns ()
modifies glob;
{
  var res : int;
  call res := foo(7);
} 
