//#Unsafe
//author: Numair Mansur (numair.mansur@gmail.com)
// Program where there is an alternative path to a location in counter example. But that alternative
// path passes through the parent state. To fix that, we made the parent state forbidden, i.e it is not
// allowed to have the parent state in the alternative path.
procedure foo()
{
  var x: int;
  x := 0;
  while(x<2) 
  {
    assert( x == 1);
    x := x+1;
  }
}
