var globalVar : int;

procedure f(x : int) returns (y : int);
requires x >= 0;
ensures y >= 0;
modifies globalVar;

implementation f(y: int) returns (x: int)
{
  x := y;
  globalVar := x;
}


