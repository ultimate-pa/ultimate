
procedure SimpleLoop(a: int) returns (res: int);

implementation SimpleLoop(a: int) returns (res: int)
{
	var z : int;
	z := a;
	if(z>150){
		z := 0;
		res := z;
		return;
	}
	
	while (z<100){
		z := z +1 ;
	}
	
	res := z;
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := SimpleLoop(a);
}