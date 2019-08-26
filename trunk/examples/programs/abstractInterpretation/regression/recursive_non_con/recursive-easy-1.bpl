//#Safe

procedure ULTIMATE.start()
{
  var z : int;
  call z := subToZero(3, 1);    
  assert(z == 0);       
}                       

procedure subToZero(a, b : int) returns (res : int)
{ 
  if(a > 0 && b > 0)
  {
	call res := subToZero(a-1, b);
  }
  else if(b < 0)
  {
    res := 0;
  }
  else
  {
	res := a;
  }
}