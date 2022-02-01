
procedure NestedLoop(a: int) returns (res: int);

implementation NestedLoop(a: int) returns (res: int)
{
	var y,z : int;
	z := a;
	y := a;
	
	while (z<100){
		while (y<100){
			z := z + 1;
			y := y + 1;
		}
		z := z+y;
	}
	
	res := z;
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := NestedLoop(a);
}