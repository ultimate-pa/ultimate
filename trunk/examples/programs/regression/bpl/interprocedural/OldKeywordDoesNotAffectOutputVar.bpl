//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-07-23
 * 
 * ProcedureInliner crashes if non-global variable occurs in `old` expression.
 *
 */


procedure foo(x : int) returns (result : int)
{
  result := x;
  result := result + 1;
  assert old(result) == 8;
}

procedure ULTIMATE.start() returns ()
{
  var res : int;
  call res := foo(7);
} 
