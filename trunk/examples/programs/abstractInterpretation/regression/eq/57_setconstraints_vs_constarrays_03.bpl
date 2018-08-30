
//#Safe
/*
 */
procedure main() {
  var i, j, k, l, m : int;
  var a, b : [int] int;

  a := ~const~Array~Int~Int(0);

  a[i] := 1;

  a[j] := 2;

  a[k] := 3;

  a[l] := 4;

  // a[m] in {0, 1, 2, 3, 4}
  assert a[m] == 0 || a[m] == 1 || a[m] == 2 || a[m] == 3 || a[m] == 4;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);
