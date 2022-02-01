
procedure SimpleTrace(a: int) returns (res: int);

implementation SimpleTrace(a: int) returns (res: int)
{
	var y,z : int;
	z := a;
	y := a;

	
	res := z;
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := SimpleTrace(a);
}