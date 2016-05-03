//#Unsafe
//author: Numair Mansur (numair.mansur@gmail.com)
procedure foo()
{
  var y: int;
  var x: int;
  x := 0;
  y := 0;
  if(y==0) 
  {
    x := 1;
  }
  else 
  {
    y := 2;
    y := 3;
    y := 4;
  }
  assert(x == 0);
}

