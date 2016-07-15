//#Safe
/* Simple procedure call.
 */

procedure ULTIMATE.start()
{
  var a,b,c : int;
  a := -1;
  b := 1;
  call c := foo(a+b);
  assert(c == 0);
}

procedure foo(y : int) returns (res : int)
{ 
	res := y;
}
