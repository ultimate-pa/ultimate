//#Safe
//author: nutz@informatik.uni-freiburg.de
procedure foo()
{
  var y: int;
  var x: int;

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

