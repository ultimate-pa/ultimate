//#Safe

procedure ULTIMATE.start()
{
  var z : int;
  call z := foo(10);    
  assert(z == 0);       
} 

procedure foo(a : int) returns (res : int)
{ 
  if(a > 0)
  {
	call res := foo(a-1);
	assert res <= a - 1;
  } else{
	res := a;
  }
}