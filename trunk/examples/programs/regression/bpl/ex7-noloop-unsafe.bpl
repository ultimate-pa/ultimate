//#Unsafe
//nutz@informatik.uni-freiburg.de
procedure foo()
{
  var y: int;

  y := 0;    
    
  if(*) {
    y := 1;
  }
  else {
    y := 2;
  }
  assert(y == 0);
}

