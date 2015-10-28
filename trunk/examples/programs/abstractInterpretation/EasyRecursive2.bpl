//#Safe
/*
 * 
 *
 */


procedure main()
{
  var i, x, y, z : int;

  i := 0;
  
  while(i < 100)
  {  
	x := 4;
	y := 6;
	
	call z := add(x, y);

	assert(z == x + y);
	 
	i := i + 1;
  }
}

procedure add(a, b : int) returns (res : int)
{ 
  if(b > 0)
  {
	call res := add(a + 2, b - 2); 	
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