procedure Main();

implementation Main()
{
  var x : int;
  var y : int;
  var z : int;
  
  x := 0;
  y := 0;
  z := 0;
   
  while(*){
	while(*){
		x := x + 1;
		y := y + 1;
		z := x + y;
	}
	z := 1;
	
  }
  z := 2;
  assert x - y == z;
}

procedure ~init() returns();  
modifies ;

implementation ~init() returns()
{

}