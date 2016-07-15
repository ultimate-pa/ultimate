//#Unsafe
/*
 * Calling two functions in an alternating fashion
 *
 */


procedure ULTIMATE.start()
{
  var x : int;
	
  call x := dispatch(2000, 2000);
  
  assert(x >= 0);
}


procedure dispatch(a, b : int) returns (res : int)
{ 
	if( a < 0 )
	{
		res := b;
		return;
	}
	
	if( a > b )
	{
		call res := funA(a, b);
	}
	else
	{
		call res := funB(a, b);	
	}
}

procedure funA(a, b : int) returns (res : int)
{ 
	call res := dispatch( a - 2, b - 1 );
}


procedure funB(a, b : int) returns (res : int)
{ 
	call res := dispatch( a - 1, b - 2 );
}

