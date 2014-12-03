var globalVar : int;

procedure f1(x : int) returns (y : int);
modifies globalVar;

procedure f2()
{
   var localVar : int;
   call localVar := id(5);
}

procedure f3()
modifies globalVar;
{
   call globalVar := id(5);
}

implementation f1(x: int) returns (y: int)
{
  y := x;
  globalVar := y;
}

