// #Unsafe
// author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//
// Aberrant conglomerate. In the conglomerate not one statement
// is aberrant. This is because x = 1 and y = 1 together are
// aberrant.

procedure foo()
{
  var x: int;
  var a: int;
  var y: int;
  
  a := 1;
  if(a==1)
  {
    x := 1;
    y := 1;
  }
  assert(x != 1 && y != 1);
}
