//#Safe
/*
 * 
 * Date: 
 * Author: 
 *
 */

procedure multiDimArry()
{
  var a : [int, int]int;
  var i : int;

  a[1,1] := 10;
  i := 2;
  while (i < 10) {
    a[i,i] := i;
    i := i+1;
  }
  assert (a[1,1] < a[i-1, i-1]);
}

