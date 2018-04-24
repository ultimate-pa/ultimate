// #Unsafe
// author: Numair Mansur(mansurm@informatik.uni-freiburg.de)
// Simple Call and Return example.



procedure F(z:int) returns (r:int)
{
  r := z+1;
}

procedure main()
{
  var c: int;
  var x: int;

  call c := F(1);
  
  
  assert(c!=2);
}
