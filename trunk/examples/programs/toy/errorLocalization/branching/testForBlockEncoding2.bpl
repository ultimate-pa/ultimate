// #Unsafe
// author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//
// With block encoding enabled, the initial assignment to C
// is aberrant. Going in the else branch will avoid the error.

procedure foo()
{
  var c: int;
  var x: int;
  var y: int;
  
  x := 2;
  c := 1;
  

  if(c==1)
  {
    c := 2;
    if(c == 2){
      y := 2;
    }
  } else {
    x := 1;
  }

  assert(x!=2);
}
