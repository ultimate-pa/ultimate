//#mSafe
//author: nutz@informatik.uni-freiburg.de
procedure ex6()
{
  var x : int;
  var b : bool;
 
  x := 1;
  b := false;

  if(b) {
    x := 0;
  }

  assert(x != 0);
}
