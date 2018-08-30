//#Safe
/*
 */
procedure main() {
  var i : int;
  var a : [int] int;

  a := ~const~Array~Int~Int(0);

  a[i] := 1;
  havoc i;

  a[i] := 2;
  havoc i;

  a[i] := 3;
  havoc i;

  a[i] := 4;
  havoc i;

  // a[m] in {0, 1, 2, 3, 4}
  assert a[i] == 0 || a[i] == 1 || a[i] == 2 || a[i] == 3 || a[i] == 4;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);
