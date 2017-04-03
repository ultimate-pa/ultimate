//#Safe
/*
 * 
 *
 */


procedure main()
{
  var i: int;
  var arr : [int]int;
  var arr2 : [int]int;
  
  i := 0;
  while(i <= 10)
  {
	arr[i] := i;	
	i := i + 1;
  }
  arr2 := arr;
  
  arr2 := arr[0 := 10];
  
  i := 0;
  while(i < 10)
  {
	assert( arr[i] >= 0 && arr[i] <= 10 );
	assert( arr2[i] >= 0 && arr2[i] <= 10 );
	i := i + 1;
  }
}