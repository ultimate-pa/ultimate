//#Safe

procedure ULTIMATE.start()
{
  var x : int;
  var b : bool;
  x := 1;
  call b := foo(x);

  assert b;
}

procedure foo(a : int) returns (ret : bool)
{ 
	ret := a > 0;
}