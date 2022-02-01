//#Safe
/* Procedure call with boolean values.
 */

procedure ULTIMATE.start()
{
  var x : int;
  assume(x >= 0);
  call x := foo(x != 0);
  assert(x == 0);
}

procedure foo(b : bool) returns (res : int)
{ 
	var i : int;
	i := 0;
	res := i;
}
