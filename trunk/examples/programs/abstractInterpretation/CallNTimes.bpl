//#Safe
/*
 * 
 *
 */


procedure main()
{
  var x, y : int;
	
  y := 1;
  x := 0;
  while(y < 10)
  {
	call x := nRec(x, y);
	y := y + 1;
  }
  
  assert(y == 10);
  assert(x > 10);
}

procedure nRec(a, i : int) returns (res : int)
{ 
	if(i == 0)
	{
		res := a;
	}
	else
	{
		call res := nRec(a + 1, i - 1); 
	}
}