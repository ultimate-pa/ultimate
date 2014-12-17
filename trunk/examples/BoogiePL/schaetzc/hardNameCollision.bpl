var globalVar : int;

procedure f(a : int, b : int, c : int, d : int)
  returns (x : int, y : int, z : int);
requires a + (b * c) - d > 0 && a + b * b + a < d - c; 
ensures a + b + c + d + x + y + z
  > (z * c) + (a * y - (a * a));
modifies globalVar;

implementation f(z : int, a : int, c : int, y : int)
  returns (x : int, b : int, d : int)
{
  d := (z + a) - (c + y);
  b := (a + c) - (y + z);
  x := b - d;
  globalVar := b + c * c * a - d;
}


