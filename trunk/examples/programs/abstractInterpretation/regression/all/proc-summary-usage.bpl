//#Safe

procedure ULTIMATE.start()
{
  var x,y : int;
  x := 0;
  y := 0;
  call x := foo(x);
  call x := foo(y);
  assert x == 1;
}

procedure foo(a : int) returns (ret : int)
{ 
	ret := a + 1;
}