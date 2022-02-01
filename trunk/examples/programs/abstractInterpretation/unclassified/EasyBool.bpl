//#Safe
/*
 * 
 *
 */


procedure main()
{
  var x : int;
  var b : bool;
  
  b := false;
  x := 10;
  
  while( x >= 0 )
  {
	if( x == 0 )
	{
	  b := true;
	}
  }
  
  assert(b && x < 10);
}