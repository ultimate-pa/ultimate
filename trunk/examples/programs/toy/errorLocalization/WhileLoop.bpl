//#Unsafe
//author: Numair Mansur (numair.mansur@gmail.com)
//While Loop
procedure foo()
{

  var y: int;
  var x: int;
  var z: int;
  var i: int;

  y := 0;
  z := 0;
  i := 0;

  while(i < 5) 
  {
    x := y;
    y := y+1;
    i := i+1;
  }

  assert(x == 5);
}

