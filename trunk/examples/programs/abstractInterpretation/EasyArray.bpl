//#Safe
/*
 * 
 *
 */


procedure main()
{
  var i: int;
  var arr : [int]int;
  
  i := 0;
  while(i <= 10)
  {
	arr[i] := i;	
	i := i + 1;
  }
  
  i := 0;
  while(i < 10)
  {
	assert( arr[i] >= 0 && arr[i] <= 10 );
	i := i + 1;
  }
}