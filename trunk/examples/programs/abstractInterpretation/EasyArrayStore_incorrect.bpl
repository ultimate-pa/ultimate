//#Unsafe
/*
 * 
 *
 */


procedure main()
{
  var i: int;
  var arr : [int]int;
  var arr2 : [int]int;
  
  
  arr2 := arr;
  arr2 := arr[0 := 20];
  
  
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
  
  assert(arr2[0] < 10); 
}