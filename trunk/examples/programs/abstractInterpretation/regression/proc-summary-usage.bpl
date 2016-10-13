//#Safe

procedure ULTIMATE.init()
{
  var x : int;
  x := 0;
  while (x < 10){
	call x := foo(x);
  }
  assert x == 10;
}

procedure foo(a : int) returns (ret : int)
{ 
	ret := a + 1;
}