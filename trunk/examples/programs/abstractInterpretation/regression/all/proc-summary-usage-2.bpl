//#Safe

procedure ULTIMATE.start()
{
  var x,y,z : int;
  x := 0;
  y := 0;
  z := 0;
  call x := foo(x);
  call x := foo(y);
  call x := foo(z);
  assert x == 2;
}

procedure foo(a : int) returns (ret : int)
{ 
	call ret := bar(a+1);
}

procedure bar(b : int) returns (ret : int)
{ 
	ret := b + 1;
}