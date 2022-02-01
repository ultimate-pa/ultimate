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

  call x := F(1);
  c := 2;
  
  assert(c!=2);
}