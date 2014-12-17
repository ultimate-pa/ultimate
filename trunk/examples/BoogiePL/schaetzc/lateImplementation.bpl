var globalVar : int;

procedure f1(x : int) returns (y : int);
requires x >= 0;
modifies globalVar;

procedure f2()
modifies globalVar;
{
   var localVar : int;
   call localVar := f1(5);
}

procedure f3()
modifies globalVar;
{
   call globalVar := f1(5);
}

implementation f1(a: int) returns (b: int)
{
  b := a;
  globalVar := b;
}

