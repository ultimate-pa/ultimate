// #Unsafe
// author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
// Simple if example.

procedure foo()
{
  var x: int;
  var c: int;

  x := 1;
  c := 10;
 
  if(c==10)
  {
    c := 2;
  }
  assert(x != 1);
}
