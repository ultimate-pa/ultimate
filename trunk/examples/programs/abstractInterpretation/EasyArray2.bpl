//#Safe
/*
 * 
 *
 */


procedure main()
{
  var i, max : int;
  var arr : [int]int;
  
  arr[0] := 0;
  
  i := 0;  
  while( i < 10 )
  {
	if(*)
	{
		arr[i] := 10 - i;
	}
  }
  
  i := 0;  
  max := -1;
  while( i < 10 )
  {
	if(arr[i] > max)
	{
		max := arr[i];
	}
  }
  
  assert(max >= 0 && max <= 10);
}