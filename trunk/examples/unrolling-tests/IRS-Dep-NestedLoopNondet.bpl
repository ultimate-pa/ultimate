
procedure NestedLoop(a: int) returns (res: int);

implementation NestedLoop(a: int) returns (res: int)
{
	var y,z : int;
	z := a;
	y := a;
	
	while (*){
		while (*){
			z := z + 1;
			y := y + 1;
		}
	}
	
	res := z;
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := NestedLoop(a);
}
3^0 