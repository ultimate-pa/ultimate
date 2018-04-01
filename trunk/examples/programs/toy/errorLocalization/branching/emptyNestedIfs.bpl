// #Unsafe
// author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//
// Nested ifs example in boogie.
// The example reveals a problem in the current
// implementation of block encoding. Alternative
// paths must also be block encoded.

procedure foo()
{
  var x: int;
  var y: int;
  var z: int;
  
  havoc x;
  havoc y;
  z := 1;
  

  if(x==1)
  {
    if(y == 2){
    }
  }
  assert(z != 1);
}
