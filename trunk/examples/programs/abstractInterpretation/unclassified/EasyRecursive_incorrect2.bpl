//#Unsafe
/*
 * 
 */


procedure main()
{
  var z : int;

  z:= 4;  
    
  call z := add(4, 3);
  
  assert(z <= 6 || z >= 8);
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