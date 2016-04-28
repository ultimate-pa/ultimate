//#Unsafe
//author: numair
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
