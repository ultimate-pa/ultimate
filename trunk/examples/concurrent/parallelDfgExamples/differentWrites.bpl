//#unsafe
// author: nutz

var x, y : int;

procedure ~init() returns();

implementation ~init() {
  assume x == 0;
}

procedure T1() returns ();
modifies x;

implementation T1() 
{
  x := 1;
  x := 2;
}

procedure T2() returns () ;
modifies y;

implementation T2() 
{
  y := x;
  assert y == 2;
}
