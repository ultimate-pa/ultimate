//#Safe

procedure ULTIMATE.start()
{
  var z : int;
  var x, y : int;
  x := -2 + -3;
  y := 10;
  call z := add(5, 3);    
  assert(z == 8);       
}                       

procedure add(a, b : int) returns (res : int)
{ 
  if(b > 0)
  {
	call res := add(a + 1, b - 1);
  }
  else if(b < 0)
  {
    call res := add(a - 1, b + 1);
  }
  else
  {
	res := a;
  }
}
