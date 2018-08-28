//#Safe
/*
 */
procedure main() {
  var i, j : int;
  var a, b : [int] int;

  a := ~const~Array~Int~Int(0);

  a[i] := 1;
  havoc i;

  a[i] := 2;
  havoc i;

  // a -- a[q] = 1 \/ a[q] = 2 -- (const 0) holds
  // --> we can infer a[j] in {0, 1, 2}

  assert a[j] == 0 || a[j] == 1 || a[j] == 2;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);
