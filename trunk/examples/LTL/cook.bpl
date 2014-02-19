var  x,n: int;

procedure ULTIMATE.start() returns ()
modifies x,n;
{	
 x := 1;
 havoc n;
  while(n > 0)
  {
	n:= n-1;
  }
  x:=0;
}