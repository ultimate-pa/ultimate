//#Unsafe
//author: Numair Mansur (numair.mansur@gmail.com)
// When there are two assertions in the program and there is an alternative path
// to the error trace (Always the last state) through the other assert statement.
// In this case, just don't consider the last statement in the list of possible end points for 
// the alternative error trace.
procedure foo()
{
  var x: int;
  if(*) 
  {
    x := 0;
    assert(x==1);
  }
assert(false);
}
