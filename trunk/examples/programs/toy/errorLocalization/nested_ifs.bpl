//#Unsafe
//author: Numair Mansur (numair.mansur@gmail.com)
//Nested Ifs
procedure foo()
{
  var y: int;
  var x: int;
  var z: int;
  
  y := 0;
  z := 0;
  if(y==0) 
  {
    x := 1;
    if(z==0)
    {
      z := 1;
    }
  }
  else 
  {
    y := 2;
    y := 3;
    y := 4;
  }
  assert(x == 0);
}

