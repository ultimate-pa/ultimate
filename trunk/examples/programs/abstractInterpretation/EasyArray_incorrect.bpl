//#Unsafe
/*
 * 
 *
 */


procedure main()
{
  var i : int;
  var arr : [int]int;
  
  arr[0] := 11;
  arr[1] := 22;
  
  i := 123;
  
  assert( arr[0] == 22 );
}