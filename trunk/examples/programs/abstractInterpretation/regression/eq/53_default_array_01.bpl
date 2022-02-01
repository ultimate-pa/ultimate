//#Safe
procedure foo() {
  var a : [int] int;
  var i : int;

  a := ~const~Array~Int~Int(0);

  assert a[i] == 0;
}

function { :smtdefined "((as const (Array Int Int)) in)" } ~const~Array~Int~Int(in : int) returns (out : [int] int);

