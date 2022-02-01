//#Unsafe
/*
 * Calling two functions in an alternating fashion
 *
 */


procedure ULTIMATE.start()
{
  var x : int;
	
  call x := dispatch(20);
  
  assert(x >= 0);
}


procedure dispatch(z : int) returns (res : int)
{ 
	if( z < 0 )
	{
		res := z;
		return;
	}
	
	if( * )
	{
		call res := funA(z);
	}
	else
	{
		call res := funB(z);	
	}
}

procedure funA(a : int) returns (res : int)
{ 
	call res := dispatch( a - 1 );
}


procedure funB(b : int) returns (res : int)
{ 
	call res := dispatch( b - 2 );
}

