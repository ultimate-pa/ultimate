// #Unsafe
// author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//
// Aberrant conglomerate. But the aberrant statement is not in
// the branch.

procedure foo()
{
  var x: int;
  var a: int;
  
  a := 1;
  havoc x;
  if(x==1)
  {
    x := 2;
  } else {
    a := 2;  
  }
  assert(a != 1);
}
