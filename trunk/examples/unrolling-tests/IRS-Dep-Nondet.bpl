
procedure Nondet(a: int) returns (res: int);

implementation Nondet(a: int) returns (res: int)
{
	var y,z : int;
	z := a;
	y := a;
	if(*){
		z := 1;
	}else {
		z := 1;
	}


	
	res := z;
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := Nondet(a);
}