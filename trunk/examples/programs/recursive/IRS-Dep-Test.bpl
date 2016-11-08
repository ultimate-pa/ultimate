

var b, c: int;
var x: int;

procedure McCarthyRec(x: int) returns (res: int);

implementation McCarthyRec(x: int) returns (res: int)
{
	var z : int;
	z := x;
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
  call b := McCarthyRec(a);
}