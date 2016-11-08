//#Safe
/* Simple procedure call.
 */

procedure ULTIMATE.start()
{
  var x : int;
  call x := foo();
  assert(x == 0);
}

procedure foo() returns (res : int)
{ 
	var i : int;
	i := 0;
	res := i;
}
