//#Safe
procedure foo() {
  var a : [int] int;
  var i : int;

  a := ~const~Array~Int~Int(0);

  assert a[i] == 0;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);

