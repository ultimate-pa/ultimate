//#Unsafe
//author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
//Angelic Verification

var m:[int]int ; // Global

procedure FooBar()
  modifies m;
{
  var w: int;
  call w := env1(); // Demonic Environment
  assert w > 0;
  m[w] := 2;
}

procedure Baz(z:int)
  modifies m;
{
  assert z > 0; // True Assertion Failure
  m[z] := 4;
}

// Entry point
procedure Foo() 
  modifies m;
{
  call FooBar();
  call Baz(0); // TRUE BUG
}

// Environment
procedure env1() returns ( r : int );
