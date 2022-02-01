//#Unsafe
/*
 * 
 */


procedure main()
{
  var z : int;

  //havoc x;
  //havoc y;  
  z:= 4;  
    
  call z := add(4, 3);
  
  assert(z == 4);
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
